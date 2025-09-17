/* tc-tic54x.c -- Assembly code for the Texas Instruments TMS320C54X
   Copyright (C) 1999-2025 Free Software Foundation, Inc.
   Contributed by Timothy Wall (twall@cygnus.com)

   This file is part of GAS, the GNU Assembler.

   GAS is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 3, or (at your option)
   any later version.

   GAS is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with GAS; see the file COPYING.  If not, write to the Free
   Software Foundation, 51 Franklin Street - Fifth Floor, Boston, MA
   02110-1301, USA.  */

/* Texas Instruments TMS320C54X machine specific gas.
   Written by Timothy Wall (twall@alum.mit.edu).

   Valuable things to do:
   Pipeline conflict warnings
   We encode/decode "ld #_label, dp" differently in relocatable files
     This means we're not compatible with TI output containing those
     expressions.  We store the upper nine bits; TI stores the lower nine
     bits.  How they recover the original upper nine bits is beyond me.

   Tests to add to expect testsuite:
     '=' and '==' with .if, .elseif, and .break

   Incompatibilities (mostly trivial):
   We don't allow '''
   We fill text section with zeroes instead of "nop"s
   We don't convert '' or "" to a single instance
   We don't convert '' to '\0'
   We don't allow strings with .byte/.half/.short/.long
   Probably details of the subsym stuff are different
   TI sets labels to be data type 4 (T_INT); GAS uses T_NULL.

   COFF1 limits section names to 8 characters.
   Some of the default behavior changed from COFF1 to COFF2.  */

#include "as.h"
#include <limits.h>
#include "safe-ctype.h"
#include "sb.h"
#include "macro.h"
#include "subsegs.h"
#include "opcode/tic54x.h"
#include "obj-coff.h"
#include <math.h>


static struct stag
{
  symbolS *sym;		        /* Symbol for this stag; value is offset.  */
  const char *name;		/* Shortcut to symbol name.  */
  bfd_vma size;		        /* Size of struct/union.  */
  int current_bitfield_offset;  /* Temporary for tracking fields.  */
  int is_union;
  struct stag_field		/* List of fields.  */
  {
    const char *name;
    bfd_vma offset;		/* Of start of this field.  */
    int bitfield_offset;	/* Of start of this field.  */
    struct stag *stag;	        /* If field is struct/union.  */
    struct stag_field *next;
  } *field;
  /* For nesting; used only in stag construction.  */
  struct stag *inner;	        /* Enclosed .struct.  */
  struct stag *outer;	        /* Enclosing .struct.  */
} *current_stag = NULL;

#define MAX_LINE 256 /* Lines longer than this are truncated by TI's asm.  */

typedef struct _tic54x_insn
{
  const insn_template *tm;	/* Opcode template.  */

  char mnemonic[MAX_LINE];	/* Opcode name/mnemonic.  */
  char parmnemonic[MAX_LINE];   /* 2nd mnemonic of parallel insn.  */

  int opcount;
  struct opstruct
  {
    char buf[MAX_LINE];
    enum optype type;
    expressionS exp;
  } operands[MAX_OPERANDS];

  int paropcount;
  struct opstruct paroperands[MAX_OPERANDS];

  int is_lkaddr;
  int lkoperand;
  int words;			/* Size of insn in 16-bit words.  */
  int using_default_dst;	/* Do we need to explicitly set an
				   omitted OP_DST operand?  */
  struct
  {
    unsigned short word;	     /* Final encoded opcode data.  */
    int unresolved;
    int r_nchars;		     /* Relocation size.  */
    bfd_reloc_code_real_type r_type; /* Relocation type.  */
    expressionS addr_expr;	     /* Storage for unresolved expressions.  */
  } opcode[3];
} tic54x_insn;

enum cpu_version
{
  VNONE = 0, V541 = 1, V542 = 2, V543 = 3, V545 = 5, V548 = 8, V549 = 9,
  V545LP = 15, V546LP = 16
};

enum address_mode
{
  c_mode,   /* 16-bit addresses.  */
  far_mode  /* >16-bit addresses.  */
};

static segT stag_saved_seg;
static subsegT stag_saved_subseg;

const char comment_chars[] = ";";
const char line_comment_chars[] = ";*#"; /* At column zero only.  */
const char line_separator_chars[] = ""; /* Not permitted.  */

int emitting_long = 0;

/* Characters which indicate that this is a floating point constant.  */
const char FLT_CHARS[] = "fF";

/* Characters that can be used to separate mantissa from exp in FP
   nums.  */
const char EXP_CHARS[] = "eE";

const char md_shortopts[] = "";

#define OPTION_ADDRESS_MODE     (OPTION_MD_BASE)
#define OPTION_CPU_VERSION      (OPTION_ADDRESS_MODE + 1)
#define OPTION_COFF_VERSION     (OPTION_CPU_VERSION + 1)
#define OPTION_STDERR_TO_FILE   (OPTION_COFF_VERSION + 1)

const struct option md_longopts[] =
{
  { "mfar-mode",       no_argument,	    NULL, OPTION_ADDRESS_MODE },
  { "mf",	       no_argument,	    NULL, OPTION_ADDRESS_MODE },
  { "mcpu",	       required_argument,   NULL, OPTION_CPU_VERSION },
  { "merrors-to-file", required_argument,   NULL, OPTION_STDERR_TO_FILE },
  { "me",	       required_argument,   NULL, OPTION_STDERR_TO_FILE },
  { NULL,              no_argument,         NULL, 0},
};

const size_t md_longopts_size = sizeof (md_longopts);

static int assembly_begun = 0;
/* Addressing mode is not entirely implemented; the latest rev of the Other
   assembler doesn't seem to make any distinction whatsoever; all relocations
   are stored as extended relocations.  Older versions used REL16 vs RELEXT16,
   but now it seems all relocations are RELEXT16.  We use all RELEXT16.

   The cpu version is kind of a waste of time as well.  There is one
   instruction (RND) for LP devices only, and several for devices with
   extended addressing only.  We include it for compatibility.  */
static enum address_mode amode = c_mode;
static enum cpu_version cpu = VNONE;

/* Include string substitutions in listing?  */
static int listing_sslist = 0;

/* Did we do subsym substitutions on the line?  */
static int substitution_line = 0;

/* Last label seen.  */
static symbolS *last_label_seen = NULL;

/* This ensures that all new labels are unique.  */
static int local_label_id;

static htab_t subsym_recurse_hash; /* Prevent infinite recurse.  */
/* Allow maximum levels of macro nesting; level 0 is the main substitution
   symbol table.  The other assembler only does 32 levels, so there!  */
#define MAX_SUBSYM_HASH 100
static htab_t subsym_hash[MAX_SUBSYM_HASH];

typedef struct
{
  const char *name;
  union {
    int (*s) (char *, char *);
    float (*f) (float, float);
    int (*i) (float, float);
  } proc;
  int nargs;
  int type;
} subsym_proc_entry;

typedef struct {
  union {
    char *s;
    const subsym_proc_entry *p;
  } u;
  unsigned int freekey : 1;
  unsigned int freeval : 1;
  unsigned int isproc : 1;
  unsigned int ismath : 1;
} subsym_ent_t;


/* Keep track of local labels so we can substitute them before GAS sees them
   since macros use their own 'namespace' for local labels, use a separate hash

   We do our own local label handling 'cuz it's subtly different from the
   stock GAS handling.

   We use our own macro nesting counter, since GAS overloads it when expanding
   other things (like conditionals and repeat loops).  */
static int macro_level = 0;
static htab_t local_label_hash[MAX_SUBSYM_HASH];
/* Keep track of struct/union tags.  */
static htab_t stag_hash;
static htab_t op_hash;
static htab_t parop_hash;
static htab_t reg_hash;
static htab_t mmreg_hash;
static htab_t cc_hash;
static htab_t cc2_hash;
static htab_t cc3_hash;
static htab_t sbit_hash;
static htab_t misc_symbol_hash;

/* Only word (et al.), align, or conditionals are allowed within
   .struct/.union.  */
#define ILLEGAL_WITHIN_STRUCT()					\
  do								\
    if (current_stag != NULL)					\
      { 							\
	as_bad (_("pseudo-op illegal within .struct/.union"));	\
	return;							\
      }								\
  while (0)


static void subsym_create_or_replace (char *, char *);
static subsym_ent_t *subsym_lookup (char *, int);
static char *subsym_substitute (char *, int);


void
md_show_usage (FILE *stream)
{
  const char *options[] = {
    "C54x-specific command line options:\n",
    "-mfar-mode | -mf          Use extended addressing\n",
    "-mcpu=<CPU version>       Specify the CPU version\n",
    "-merrors-to-file <filename>\n",
    "-me <filename>            Redirect errors to a file\n"
  };
  
  const int NUM_OPTIONS = 5;
  
  for (int i = 0; i < NUM_OPTIONS; i++)
  {
    fprintf (stream, _("%s"), options[i]);
  }
}

/* Output a single character (upper octet is zero).  */

static void
tic54x_emit_char (char c)
{
  expressionS expn;

  expn.X_op = O_constant;
  expn.X_add_number = c;
  emit_expr (&expn, 2);
}

/* Walk backwards in the frag chain.  */

static fragS *
frag_prev (fragS *frag, segT seg)
{
  segment_info_type *seginfo = seg_info (seg);
  fragS *fragp;

  for (fragp = seginfo->frchainP->frch_root; fragp; fragp = fragp->fr_next)
    if (fragp->fr_next == frag)
      return fragp;

  return NULL;
}

static fragS *
bit_offset_frag (fragS *frag, segT seg)
{
  while (frag != NULL)
    {
      if (frag->fr_fix != 0 || frag->fr_opcode != NULL || frag->tc_frag_data != 0)
        return frag;
      frag = frag_prev (frag, seg);
    }
  return NULL;
}

/* Return the number of bits allocated in the most recent word, or zero if
   none. .field/.space/.bes may leave words partially allocated.  */

static int
frag_bit_offset (fragS *frag, segT seg)
{
  frag = bit_offset_frag (frag, seg);

  if (!frag)
    return 0;

  return frag->fr_opcode != NULL ? -1 : frag->tc_frag_data;
}

/* Read an expression from a C string; returns a pointer past the end of the
   expression.  */

static char *parse_expression(char *str, expressionS *expn)
{
    char *saved_input_line_pointer = input_line_pointer;
    input_line_pointer = str;
    expression(expn);
    char *result = input_line_pointer;
    input_line_pointer = saved_input_line_pointer;
    return result;
}

/* .asg "character-string"|character-string, symbol

   .eval is the only pseudo-op allowed to perform arithmetic on substitution
   symbols.  all other use of symbols defined with .asg are currently
   unsupported.  */

static char* extract_quoted_string(void)
{
    int len;
    return demand_copy_C_string(&len);
}

static char* extract_unquoted_string(void)
{
    size_t len;
    char *str = input_line_pointer;
    int c;
    
    while ((c = *input_line_pointer) != ',')
    {
        if (is_end_of_stmt(c))
            break;
        ++input_line_pointer;
    }
    
    len = input_line_pointer - str;
    return notes_memdup(str, len, len + 1);
}

static char* get_string_argument(int *c)
{
    int quoted = *input_line_pointer == '"';
    char *str;
    
    if (quoted)
    {
        str = extract_quoted_string();
        *c = *input_line_pointer;
    }
    else
    {
        str = extract_unquoted_string();
        *c = *input_line_pointer;
    }
    
    return str;
}

static int validate_comma_separator(int c, char *str)
{
    if (c != ',')
    {
        as_bad(_("Comma and symbol expected for '.asg STRING, SYMBOL'"));
        notes_free(str);
        ignore_rest_of_line();
        return 0;
    }
    return 1;
}

static char* extract_symbol_name(void)
{
    char *name;
    int c = get_symbol_name(&name);
    name = notes_strdup(name);
    (void)restore_line_pointer(c);
    return name;
}

static int validate_symbol_name(char *name, char *str)
{
    if (!ISALPHA(*name))
    {
        as_bad(_("symbols assigned with .asg must begin with a letter"));
        notes_free(str);
        ignore_rest_of_line();
        return 0;
    }
    return 1;
}

static void
tic54x_asg(int x ATTRIBUTE_UNUSED)
{
    int c;
    char *name;
    char *str;
    
    ILLEGAL_WITHIN_STRUCT();
    
    str = get_string_argument(&c);
    
    if (!validate_comma_separator(c, str))
        return;
    
    ++input_line_pointer;
    name = extract_symbol_name();
    
    if (!validate_symbol_name(name, str))
        return;
    
    subsym_create_or_replace(name, str);
    demand_empty_rest_of_line();
}

/* .eval expression, symbol
   There's something screwy about this.  The other assembler sometimes does and
   sometimes doesn't substitute symbols defined with .eval.
   We'll put the symbols into the subsym table as well as the normal symbol
   table, since that's what works best.  */

static int parse_quoted_expression(int *value)
{
    int quoted = *input_line_pointer == '"';
    if (quoted)
        ++input_line_pointer;
    *value = get_absolute_expression();
    if (!quoted)
        return 1;
    if (*input_line_pointer != '"')
    {
        as_bad(_("Unterminated string after absolute expression"));
        return 0;
    }
    ++input_line_pointer;
    return 1;
}

static int expect_comma(void)
{
    if (*input_line_pointer++ != ',')
    {
        as_bad(_("Comma and symbol expected for '.eval EXPR, SYMBOL'"));
        return 0;
    }
    return 1;
}

static char* get_and_validate_symbol_name(void)
{
    char *name;
    char c = get_symbol_name(&name);
    
    if (!ISALPHA(*name))
    {
        as_bad(_("symbols assigned with .eval must begin with a letter"));
        (void)restore_line_pointer(c);
        return NULL;
    }
    
    name = notes_strdup(name);
    (void)restore_line_pointer(c);
    return name;
}

static void create_eval_symbol(const char *name, int value)
{
    symbolS *symbolP = symbol_new(name, absolute_section, &zero_address_frag, value);
    SF_SET_LOCAL(symbolP);
    symbol_table_insert(symbolP);
}

static void update_subsym_table(const char *name, int value)
{
    char valuestr[32];
    sprintf(valuestr, "%d", value);
    char *tmp = notes_strdup(valuestr);
    subsym_create_or_replace(name, tmp);
}

static void
tic54x_eval(int x ATTRIBUTE_UNUSED)
{
    int value;
    char *name;

    ILLEGAL_WITHIN_STRUCT();
    SKIP_WHITESPACE();

    if (!parse_quoted_expression(&value))
    {
        ignore_rest_of_line();
        return;
    }

    if (!expect_comma())
    {
        ignore_rest_of_line();
        return;
    }

    name = get_and_validate_symbol_name();
    if (!name)
    {
        ignore_rest_of_line();
        return;
    }

    create_eval_symbol(name, value);
    update_subsym_table(name, value);
    demand_empty_rest_of_line();
}

/* .bss symbol, size [, [blocking flag] [, alignment flag]

   alignment is to a longword boundary; blocking is to 128-word boundary.

   1) if there is a hole in memory, this directive should attempt to fill it
      (not yet implemented).

   2) if the blocking flag is not set, allocate at the current SPC
      otherwise, check to see if the current SPC plus the space to be
      allocated crosses the page boundary (128 words).
      if there's not enough space, create a hole and align with the next page
      boundary.
      (not yet implemented).  */

static int parse_bss_name(char **name)
{
    char c = get_symbol_name(name);
    if (c == '"')
        c = *++input_line_pointer;
    if (c != ',')
    {
        as_bad(_(".bss size argument missing\n"));
        ignore_rest_of_line();
        return 0;
    }
    ++input_line_pointer;
    return 1;
}

static int parse_bss_size(offsetT *words)
{
    *words = get_absolute_expression();
    if (*words < 0)
    {
        as_bad(_(".bss size %d < 0!"), (int)*words);
        ignore_rest_of_line();
        return 0;
    }
    return 1;
}

static void parse_optional_arguments(int *block, int *align)
{
    *block = 0;
    *align = 0;
    
    if (*input_line_pointer != ',')
        return;
    
    ++input_line_pointer;
    if (*input_line_pointer != ',')
        *block = get_absolute_expression();
    
    if (*input_line_pointer != ',')
        return;
    
    ++input_line_pointer;
    *align = get_absolute_expression();
}

static void setup_bss_symbol(symbolS *symbolP, offsetT words)
{
    if (S_GET_SEGMENT(symbolP) == bss_section)
        symbol_get_frag(symbolP)->fr_symbol = NULL;
    
    symbol_set_frag(symbolP, frag_now);
    char *p = frag_var(rs_org, 1, 1, 0, symbolP, words * OCTETS_PER_BYTE, NULL);
    *p = 0;
    
    S_SET_SEGMENT(symbolP, bss_section);
    
    if (S_GET_STORAGE_CLASS(symbolP) != C_EXT)
        S_SET_STORAGE_CLASS(symbolP, C_STAT);
}

static void apply_alignment(int align)
{
    if (!align)
        return;
    
    s_align_bytes(4);
    --input_line_pointer;
}

static void apply_block_flag(int block)
{
    if (block)
        bss_section->flags |= SEC_TIC54X_BLOCK;
}

static void tic54x_bss(int x ATTRIBUTE_UNUSED)
{
    char *name;
    offsetT words;
    int block;
    int align;
    
    ILLEGAL_WITHIN_STRUCT();
    
    segT current_seg = now_seg;
    subsegT current_subseg = now_subseg;
    
    if (!parse_bss_name(&name))
        return;
    
    if (!parse_bss_size(&words))
        return;
    
    parse_optional_arguments(&block, &align);
    
    subseg_set(bss_section, 0);
    symbolS *symbolP = symbol_find_or_make(name);
    setup_bss_symbol(symbolP, words);
    apply_alignment(align);
    apply_block_flag(block);
    
    subseg_set(current_seg, current_subseg);
    demand_empty_rest_of_line();
}

static char* build_field_path(const char *path, const char *field_name)
{
    return concat(path, *path ? "." : "", field_name, (const char *) NULL);
}

static void create_absolute_symbol(const char *name, bfd_vma offset)
{
    symbolS *sym = symbol_new(name, absolute_section, &zero_address_frag, offset);
    SF_SET_LOCAL(sym);
    symbol_table_insert(sym);
}

static void create_subsym_entry(const char *name, symbolS *rootsym, const char *root_stag_name)
{
    subsym_ent_t *ent = xmalloc(sizeof(*ent));
    ent->u.s = concat(S_GET_NAME(rootsym), "+", root_stag_name,
                     name + strlen(S_GET_NAME(rootsym)),
                     (const char *) NULL);
    ent->freekey = 1;
    ent->freeval = 1;
    ent->isproc = 0;
    ent->ismath = 0;
    str_hash_insert(subsym_hash[0], name, ent, 0);
}

static bfd_vma calculate_field_offset(struct stag_field *field, bfd_vma base_offset)
{
    return field->stag ? field->offset : base_offset + field->offset;
}

static void process_field_symbol(struct stag_field *field, const char *name,
                                bfd_vma base_offset, symbolS *rootsym,
                                const char *root_stag_name)
{
    if (rootsym == NULL)
    {
        create_absolute_symbol(name, calculate_field_offset(field, base_offset));
    }
    else
    {
        create_subsym_entry(name, rootsym, root_stag_name);
    }
}

static void process_nested_structure(struct stag_field *field, const char *name,
                                    symbolS *rootsym, const char *root_stag_name)
{
    if (field->stag != NULL)
    {
        stag_add_field_symbols(field->stag, name, field->offset,
                              rootsym, root_stag_name);
    }
}

static void stag_add_field_symbols(struct stag *stag,
                                  const char *path,
                                  bfd_vma base_offset,
                                  symbolS *rootsym,
                                  const char *root_stag_name)
{
    char *prefix = concat(path, *path ? "." : "", (const char *) NULL);
    struct stag_field *field = stag->field;

    while (field != NULL)
    {
        char *name = concat(prefix, field->name, (const char *) NULL);
        
        process_field_symbol(field, name, base_offset, rootsym, root_stag_name);
        process_nested_structure(field, name, rootsym, root_stag_name);
        
        if (rootsym == NULL)
        {
            free(name);
        }
        
        field = field->next;
    }
    
    free(prefix);
}

/* Keep track of stag fields so that when structures are nested we can add the
   complete dereferencing symbols to the symbol table.  */

static struct stag_field* create_stag_field(const char *name, bfd_vma offset, struct stag *parent, struct stag *stag)
{
  struct stag_field *sfield = XCNEW(struct stag_field);
  sfield->name = xstrdup(name);
  sfield->offset = offset;
  sfield->bitfield_offset = parent->current_bitfield_offset;
  sfield->stag = stag;
  return sfield;
}

static struct stag_field* find_last_field(struct stag_field *field)
{
  while (field->next != NULL)
    field = field->next;
  return field;
}

static void append_field_to_parent(struct stag *parent, struct stag_field *sfield)
{
  if (parent->field == NULL) {
    parent->field = sfield;
    return;
  }
  
  struct stag_field *last = find_last_field(parent->field);
  last->next = sfield;
}

static void create_field_symbol_if_needed(struct stag *parent, const char *name, bfd_vma offset)
{
  #define FAKE_PREFIX ".fake"
  
  if (!startswith(parent->name, FAKE_PREFIX))
    return;
    
  symbolS *sym = symbol_new(name, absolute_section, &zero_address_frag, offset);
  SF_SET_LOCAL(sym);
  symbol_table_insert(sym);
}

static void stag_add_field(struct stag *parent, const char *name, bfd_vma offset, struct stag *stag)
{
  struct stag_field *sfield = create_stag_field(name, offset, parent, stag);
  append_field_to_parent(parent, sfield);
  create_field_symbol_if_needed(parent, name, offset);
}

/* [STAG] .struct       [OFFSET]
   Start defining structure offsets (symbols in absolute section).  */

static void switch_to_absolute_section(void)
{
    stag_saved_seg = now_seg;
    stag_saved_subseg = now_subseg;
    subseg_set(absolute_section, 0);
}

static void align_current_bitfield(void)
{
    if (current_stag && current_stag->current_bitfield_offset != 0)
    {
        ++abs_section_offset;
        current_stag->current_bitfield_offset = 0;
    }
}

static int get_start_offset(int is_union)
{
    if (is_union)
        return 0;
    
    SKIP_WHITESPACE();
    if (!is_end_of_stmt(*input_line_pointer))
        return get_absolute_expression();
    return 0;
}

static struct stag* create_nested_stag(int start_offset)
{
    current_stag->inner = XCNEW(struct stag);
    current_stag->inner->outer = current_stag;
    
    if (start_offset)
        as_warn(_("Offset on nested structures is ignored"));
    
    return current_stag->inner;
}

static struct stag* create_new_stag(int start_offset)
{
    abs_section_offset = start_offset;
    return XCNEW(struct stag);
}

static char* generate_fake_label(void)
{
    static int struct_count = 0;
    char fake[] = ".fake_stagNNNNNNN";
    sprintf(fake, ".fake_stag%d", struct_count++);
    return xstrdup(fake);
}

static void create_stag_symbol(void)
{
    char* name;
    
    if (line_label == NULL)
    {
        name = generate_fake_label();
        current_stag->sym = symbol_new(name, absolute_section,
                                      &zero_address_frag,
                                      abs_section_offset);
        free(name);
    }
    else
    {
        name = xstrdup(S_GET_NAME(line_label));
        current_stag->sym = symbol_new(name, absolute_section,
                                      &zero_address_frag,
                                      abs_section_offset);
        free(name);
    }
    
    current_stag->name = S_GET_NAME(current_stag->sym);
    SF_SET_LOCAL(current_stag->sym);
}

static void register_global_stag(void)
{
    if (current_stag->outer == NULL)
        symbol_table_insert(current_stag->sym);
}

static void tic54x_struct(int arg)
{
    int start_offset;
    int is_union = arg;
    
    if (!current_stag)
    {
        switch_to_absolute_section();
    }
    else
    {
        align_current_bitfield();
    }
    
    start_offset = get_start_offset(is_union);
    
    if (current_stag)
    {
        current_stag = create_nested_stag(start_offset);
        start_offset = abs_section_offset;
    }
    else
    {
        current_stag = create_new_stag(start_offset);
    }
    
    current_stag->is_union = is_union;
    create_stag_symbol();
    register_global_stag();
    line_label = NULL;
}

/* [LABEL] .endstruct
   finish defining structure offsets; optional LABEL's value will be the size
   of the structure.  */

static int validate_stag_context(int is_union)
{
    if (!current_stag || current_stag->is_union != is_union)
    {
        const char *type = is_union ? "union" : "struct";
        as_bad(_(".end%s without preceding .%s"), type, type);
        ignore_rest_of_line();
        return 0;
    }
    return 1;
}

static void align_bitfield_if_needed(void)
{
    if (current_stag->current_bitfield_offset)
    {
        ++abs_section_offset;
        current_stag->current_bitfield_offset = 0;
    }
}

static int calculate_stag_size(void)
{
    if (current_stag->is_union)
        return current_stag->size;
    return abs_section_offset - S_GET_VALUE(current_stag->sym);
}

static void set_line_label_if_exists(int size)
{
    if (line_label != NULL)
    {
        S_SET_VALUE(line_label, size);
        symbol_table_insert(line_label);
        line_label = NULL;
    }
}

static void update_stag_size_if_struct(int size)
{
    if (!current_stag->is_union)
        current_stag->size = size;
}

static void register_outer_stag(void)
{
    const char *path = startswith(current_stag->name, ".fake") ? "" : current_stag->name;
    
    str_hash_insert(stag_hash, current_stag->name, current_stag, 0);
    stag_add_field_symbols(current_stag, path,
                          S_GET_VALUE(current_stag->sym),
                          NULL, NULL);
}

static void handle_nested_stag(void)
{
    stag_add_field(current_stag, current_stag->inner->name,
                   S_GET_VALUE(current_stag->inner->sym),
                   current_stag->inner);
}

static void restore_saved_segment(void)
{
    subseg_set(stag_saved_seg, stag_saved_subseg);
}

static void tic54x_endstruct(int is_union)
{
    if (!validate_stag_context(is_union))
        return;

    align_bitfield_if_needed();
    
    int size = calculate_stag_size();
    set_line_label_if_exists(size);
    update_stag_size_if_struct(size);
    
    if (current_stag->outer == NULL)
        register_outer_stag();
    
    current_stag = current_stag->outer;
    
    if (current_stag != NULL)
        handle_nested_stag();
    else
        restore_saved_segment();
}

/* [LABEL]      .tag    STAG
   Reference a structure within a structure, as a sized field with an optional
   label.
   If used outside of a .struct/.endstruct, overlays the given structure
   format on the existing allocated space.  */

static void
tic54x_tag (int ignore ATTRIBUTE_UNUSED)
{
  char *name;
  int c = get_symbol_name (&name);
  struct stag *stag = str_hash_find (stag_hash, name);

  if (!stag)
    {
      handle_missing_stag(name);
      return;
    }

  if (line_label == NULL)
    {
      as_bad (_("Label required for .tag"));
      ignore_rest_of_line ();
      return;
    }

  process_tag_label(stag);
  update_section_offset(stag);

  (void) restore_line_pointer (c);
  demand_empty_rest_of_line ();
  line_label = NULL;
}

static void
handle_missing_stag(const char *name)
{
  if (*name)
    as_bad (_("Unrecognized struct/union tag '%s'"), name);
  else
    as_bad (_(".tag requires a structure tag"));
  ignore_rest_of_line ();
}

static void
process_tag_label(struct stag *stag)
{
  char *label = xstrdup (S_GET_NAME (line_label));
  
  if (current_stag != NULL)
    {
      stag_add_field (current_stag, label,
                      abs_section_offset - S_GET_VALUE (current_stag->sym),
                      stag);
    }
  else
    {
      process_tag_symbol(label, stag);
    }
  
  free (label);
}

static void
process_tag_symbol(const char *label, struct stag *stag)
{
  symbolS *sym = symbol_find (label);
  
  if (!sym)
    {
      as_bad (_(".tag target '%s' undefined"), label);
      ignore_rest_of_line ();
      return;
    }
  
  stag_add_field_symbols (stag, S_GET_NAME (sym),
                          S_GET_VALUE (stag->sym), sym, stag->name);
}

static void
update_section_offset(struct stag *stag)
{
  if (current_stag != NULL && !current_stag->is_union)
    abs_section_offset += stag->size;
}

/* Handle all .byte, .char, .double, .field, .float, .half, .int, .long,
   .short, .string, .ubyte, .uchar, .uhalf, .uint, .ulong, .ushort, .uword,
   and .word.  */

static int get_field_size(int type)
{
    switch (type)
    {
    case 'b':
    case 'B':
    case 'c':
    case 'C':
    case 'h':
    case 'H':
    case 'i':
    case 'I':
    case 's':
    case 'S':
    case 'w':
    case 'W':
    case '*':
        return 1;
    case 'f':
    case 'l':
    case 'L':
        return 2;
    case '.':
        return 0;
    default:
        return -1;
    }
}

static int is_longword_aligned_type(int type)
{
    return type == 'f' || type == 'l' || type == 'L';
}

static int validate_bitfield_count(int count)
{
    if (count < 1 || count > 32)
    {
        as_bad(_(".field count '%d' out of range (1 <= X <= 32)"), count);
        ignore_rest_of_line();
        return 0;
    }
    return 1;
}

static void calculate_bitfield_parameters(int count, int *size, int *new_count, int *new_bitfield_offset, int *field_align)
{
    #define BITFIELD_MAX_SIZE 16
    #define BITFIELD_FULL_SIZE 32
    
    if (current_stag->current_bitfield_offset + count > BITFIELD_MAX_SIZE)
    {
        if (count == BITFIELD_FULL_SIZE)
        {
            *size = 2;
            *new_count = 1;
        }
        else if (count > BITFIELD_MAX_SIZE)
        {
            *size = 1;
            *new_count = 1;
            *new_bitfield_offset = count - BITFIELD_MAX_SIZE;
        }
        else
        {
            *new_bitfield_offset = count;
        }
    }
    else
    {
        *field_align = 0;
        *new_bitfield_offset = current_stag->current_bitfield_offset + count;
    }
}

static void apply_field_alignment(int field_align, int longword_align)
{
    if (field_align)
    {
        current_stag->current_bitfield_offset = 0;
        ++abs_section_offset;
    }
    
    if (longword_align && (abs_section_offset & 0x1))
    {
        ++abs_section_offset;
    }
}

static void add_field_label(void)
{
    int field_offset = abs_section_offset - S_GET_VALUE(current_stag->sym);
    
    if (line_label == NULL)
    {
        static int fieldno = 0;
        char fake[32];
        
        sprintf(fake, ".fake_field%d", fieldno++);
        stag_add_field(current_stag, fake, field_offset, NULL);
    }
    else
    {
        char *label = xstrdup(S_GET_NAME(line_label));
        stag_add_field(current_stag, label, field_offset, NULL);
        free(label);
    }
}

static void update_stag_size(unsigned int size, int count, int new_bitfield_offset)
{
    if (current_stag->is_union)
    {
        unsigned int total_size = size * count;
        if (current_stag->size < total_size)
        {
            current_stag->size = total_size;
        }
    }
    else
    {
        abs_section_offset += size * count;
        current_stag->current_bitfield_offset = new_bitfield_offset;
    }
}

static void tic54x_struct_field(int type)
{
    unsigned int size;
    int count = 1;
    int new_bitfield_offset = 0;
    int field_align = current_stag->current_bitfield_offset != 0;
    int longword_align = 0;
    
    SKIP_WHITESPACE();
    if (!is_end_of_stmt(*input_line_pointer))
    {
        count = get_absolute_expression();
    }
    
    size = get_field_size(type);
    if (size == -1)
    {
        as_bad(_("Unrecognized field type '%c'"), type);
        ignore_rest_of_line();
        return;
    }
    
    longword_align = is_longword_aligned_type(type);
    
    if (type == '.')
    {
        if (!validate_bitfield_count(count))
        {
            return;
        }
        calculate_bitfield_parameters(count, &size, &count, &new_bitfield_offset, &field_align);
    }
    
    apply_field_alignment(field_align, longword_align);
    add_field_label();
    update_stag_size(size, count, new_bitfield_offset);
    
    line_label = NULL;
}

/* Handle .byte, .word. .int, .long and all variants.  */

static int get_octets_for_type(int type)
{
    switch (type)
    {
    case 'l':
    case 'L':
    case 'x':
        return 4;
    case 'b':
    case 'B':
    case 'c':
    case 'C':
        return 1;
    default:
        return 2;
    }
}

static void handle_long_word_alignment(int type)
{
    if (type == 'l' || type == 'L')
    {
        frag_align (2, 0, 2);
        if (line_label != NULL)
        {
            symbol_set_frag (line_label, frag_now);
            S_SET_VALUE (line_label, frag_now_fix ());
        }
    }
}

static void check_overflow(offsetT value, int octets)
{
    #define BYTE_MAX 0xFF
    #define BYTE_MIN (-0x100)
    #define WORD_MAX 0xFFFF
    #define WORD_MIN (-0x10000)
    
    if (octets == 1)
    {
        if ((value > 0 && value > BYTE_MAX) || (value < 0 && value < BYTE_MIN))
            as_warn (_("Overflow in expression, truncated to 8 bits"));
    }
    else if (octets == 2)
    {
        if ((value > 0 && value > WORD_MAX) || (value < 0 && value < WORD_MIN))
            as_warn (_("Overflow in expression, truncated to 16 bits"));
    }
}

static void process_string_literal(void)
{
    unsigned int c;
    input_line_pointer++;
    while (is_a_char (c = next_char_of_string ()))
        tic54x_emit_char (c);
    know (input_line_pointer[-1] == '\"');
}

static int validate_non_constant_expression(expressionS *expn, int octets)
{
    if (expn->X_op != O_constant && octets < 2)
    {
        as_bad (_("Relocatable values require at least WORD storage"));
        ignore_rest_of_line ();
        return 0;
    }
    return 1;
}

static void emit_expression_with_mode(expressionS *expn, int octets)
{
    if (expn->X_op != O_constant && amode == c_mode && octets == 4)
    {
        amode = far_mode;
        emitting_long = 1;
        emit_expr (expn, 4);
        emitting_long = 0;
        amode = c_mode;
    }
    else
    {
        emitting_long = (octets == 4);
        emit_expr (expn, (octets == 1) ? 2 : octets);
        emitting_long = 0;
    }
}

static void process_expression(int octets)
{
    expressionS expn;
    
    input_line_pointer = parse_expression (input_line_pointer, &expn);
    
    if (expn.X_op == O_constant)
    {
        check_overflow(expn.X_add_number, octets);
    }
    
    if (!validate_non_constant_expression(&expn, octets))
        return;
    
    emit_expression_with_mode(&expn, octets);
}

static void tic54x_cons(int type)
{
    int octets;

    if (current_stag != NULL)
    {
        tic54x_struct_field (type);
        return;
    }

#ifdef md_flush_pending_output
    md_flush_pending_output ();
#endif

    generate_lineno_debug ();
    handle_long_word_alignment(type);
    octets = get_octets_for_type(type);

    do
    {
        if (*input_line_pointer == '"')
        {
            process_string_literal();
        }
        else
        {
            process_expression(octets);
        }
    }
    while (*input_line_pointer++ == ',');

    input_line_pointer--;
    demand_empty_rest_of_line ();
}

/* .global <symbol>[,...,<symbolN>]
   .def    <symbol>[,...,<symbolN>]
   .ref    <symbol>[,...,<symbolN>]

   These all identify global symbols.

   .def means the symbol is defined in the current module and can be accessed
   by other files.  The symbol should be placed in the symbol table.

   .ref means the symbol is used in the current module but defined in another
   module.  The linker is to resolve this symbol's definition at link time.

   .global should act as a .ref or .def, as needed.

   global, def and ref all have symbol storage classes of C_EXT.

   I can't identify any difference in how the "other" c54x assembler treats
   these, so we ignore the type here.  */

void
tic54x_global (int type)
{
  check_deprecated_usage(type);
  ILLEGAL_WITHIN_STRUCT ();
  process_global_symbols();
  demand_empty_rest_of_line ();
}

static void
check_deprecated_usage(int type)
{
  if (type == 'r')
    as_warn (_("Use of .def/.ref is deprecated.  Use .global instead"));
}

static void
process_global_symbols(void)
{
  int c;
  
  do
    {
      c = process_single_symbol();
      c = handle_separator(c);
    }
  while (c == ',');
}

static int
process_single_symbol(void)
{
  char *name;
  int c;
  symbolS *symbolP;
  
  c = get_symbol_name (&name);
  symbolP = symbol_find_or_make (name);
  c = restore_line_pointer (c);
  S_SET_STORAGE_CLASS (symbolP, C_EXT);
  
  return c;
}

static int
handle_separator(int c)
{
  if (c == ',')
    {
      input_line_pointer++;
      if (is_end_of_stmt (*input_line_pointer))
        c = *input_line_pointer;
    }
  return c;
}

static void free_tuple_key(const string_tuple_t *tuple, const subsym_ent_t *val)
{
    if (val->freekey)
        free((void *)tuple->key);
}

static void free_subsym_value(const subsym_ent_t *val)
{
    if (val->freeval)
        free(val->u.s);
}

static void free_subsym_ent(void *ent)
{
    string_tuple_t *tuple = ent;
    subsym_ent_t *val = (void *)tuple->value;
    
    free_tuple_key(tuple, val);
    free_subsym_value(val);
    free(val);
    free(ent);
}

static htab_t
subsym_htab_create (void)
{
  const size_t INITIAL_HTAB_SIZE = 16;
  return htab_create_alloc (INITIAL_HTAB_SIZE, hash_string_tuple, eq_string_tuple,
			    free_subsym_ent, xcalloc, free);
}

static void
free_local_label_ent (void *ent)
{
  string_tuple_t *tuple = ent;
  free ((void *) tuple->key);
  free ((void *) tuple->value);
  free (ent);
}

static htab_t
local_label_htab_create (void)
{
  const size_t INITIAL_HTAB_SIZE = 16;
  return htab_create_alloc (INITIAL_HTAB_SIZE, hash_string_tuple, eq_string_tuple,
			    free_local_label_ent, xcalloc, free);
}

/* Reset all local labels.  */

static void
tic54x_clear_local_labels (int ignored ATTRIBUTE_UNUSED)
{
  htab_empty (local_label_hash[macro_level]);
}

/* .text
   .data
   .sect "section name"

   Initialized section
   make sure local labels get cleared when changing sections

   ARG is 't' for text, 'd' for data, or '*' for a named section

   For compatibility, '*' sections are SEC_CODE if instructions are
   encountered, or SEC_DATA if not.
*/

static void handle_text_section(void)
{
    s_text(0);
}

static void handle_data_section(void)
{
    s_data(0);
}

static char* get_section_name(int *len)
{
    char *name = NULL;
    
    if (*input_line_pointer == '"')
    {
        name = demand_copy_C_string(len);
    }
    else
    {
        int c = get_symbol_name(&name);
        (void) restore_line_pointer(c);
    }
    
    demand_empty_rest_of_line();
    return name;
}

static void setup_named_section(void)
{
    const char *flags = ",\"w\"\n";
    int len;
    char *name = get_section_name(&len);
    
    name = concat(name, flags, (char *) NULL);
    input_scrub_insert_line(name);
    obj_coff_section(0);
}

static void assign_line_label_to_section(void)
{
    if (line_label == NULL)
        return;
        
    S_SET_SEGMENT(line_label, now_seg);
    symbol_set_frag(line_label, frag_now);
    S_SET_VALUE(line_label, frag_now_fix());
    
    if (S_GET_STORAGE_CLASS(line_label) != C_EXT)
        S_SET_STORAGE_CLASS(line_label, C_LABEL);
}

static void
tic54x_sect(int arg)
{
    ILLEGAL_WITHIN_STRUCT();
    tic54x_clear_local_labels(0);
    
    if (arg == 't')
        handle_text_section();
    else if (arg == 'd')
        handle_data_section();
    else
    {
        setup_named_section();
        assign_line_label_to_section();
    }
}

/* [symbol] .space space_in_bits
   [symbol] .bes space_in_bits
   BES puts the symbol at the *last* word allocated

   cribbed from s_space.  */

static void flush_pending_output(void)
{
#ifdef md_flush_pending_output
  md_flush_pending_output();
#endif
}

static void handle_non_constant_expression(expressionS *expn, symbolS *label, int bes)
{
  struct bit_info *bi = XNEW(struct bit_info);
  char *p;
  
  bi->seg = now_seg;
  bi->type = bes;
  bi->sym = label;
  p = frag_var(rs_machine_dependent, 65536 * 2, 1, 0,
               make_expr_symbol(expn), 0, (char *)bi);
  if (p)
    *p = 0;
}

static void set_label_position(symbolS *label, int offset)
{
  if (label != NULL)
  {
    symbol_set_frag(label, frag_now);
    S_SET_VALUE(label, frag_now_fix() + offset);
  }
}

static int handle_bit_offset(expressionS *expn, symbolS **label, int bes)
{
  const int bits_per_byte = OCTETS_PER_BYTE * 8;
  int bit_offset = frag_now->tc_frag_data;
  
  if (bit_offset == 0 || bit_offset >= 16)
    return bit_offset;
  
  int spare_bits = bits_per_byte - bit_offset;
  
  if (spare_bits >= expn->X_add_number)
  {
    set_label_position(*label, -1);
    *label = NULL;
    frag_now->tc_frag_data += expn->X_add_number;
    return -1;
  }
  
  expn->X_add_number -= spare_bits;
  if (!bes)
  {
    set_label_position(*label, -1);
    *label = NULL;
  }
  
  return bit_offset;
}

static int validate_octets(long octets)
{
  if (octets < 0)
  {
    as_warn(_(".space/.bes repeat count is negative, ignored"));
    return 0;
  }
  if (octets == 0)
  {
    as_warn(_(".space/.bes repeat count is zero, ignored"));
    return 0;
  }
  return 1;
}

static void handle_absolute_section(long words, symbolS *label, int bes, int bit_offset)
{
  abs_section_offset += words;
  if (bes && label != NULL)
    S_SET_VALUE(label, abs_section_offset - 1);
  frag_now->tc_frag_data = bit_offset;
}

static void allocate_fragment(long octets, symbolS *label, int bes, int bit_offset)
{
  char *p = NULL;
  
  if (!need_pass_2)
    p = frag_var(rs_fill, 1, 1, 0, NULL, octets, NULL);
  
  frag_now->tc_frag_data = bit_offset;
  
  if (bes && label != NULL)
  {
    symbol_set_frag(label, frag_now);
    S_SET_VALUE(label, frag_now_fix() - 1);
  }
  
  if (p)
    *p = 0;
}

static void tic54x_space(int arg)
{
  const int bits_per_byte = OCTETS_PER_BYTE * 8;
  expressionS expn;
  long words;
  int octets;
  int bit_offset;
  symbolS *label = line_label;
  int bes = arg;
  
  ILLEGAL_WITHIN_STRUCT();
  flush_pending_output();
  
  expression(&expn);
  
  if (expn.X_op != O_constant || frag_bit_offset(frag_now, now_seg) == -1)
  {
    handle_non_constant_expression(&expn, label, bes);
    return;
  }
  
  bit_offset = handle_bit_offset(&expn, &label, bes);
  if (bit_offset == -1)
    goto getout;
  
  words = (expn.X_add_number + bits_per_byte - 1) / bits_per_byte;
  bit_offset = expn.X_add_number % bits_per_byte;
  octets = words * OCTETS_PER_BYTE;
  
  if (!validate_octets(octets))
    goto getout;
  
  if (now_seg == absolute_section)
  {
    handle_absolute_section(words, label, bes, bit_offset);
    goto getout;
  }
  
  allocate_fragment(octets, label, bes, bit_offset);
  
getout:
  demand_empty_rest_of_line();
}

/* [symbol] .usect "section-name", size-in-words
		   [, [blocking-flag] [, alignment-flag]]

   Uninitialized section.
   Non-zero blocking means that if the section would cross a page (128-word)
   boundary, it will be page-aligned.
   Non-zero alignment aligns on a longword boundary.

   Has no effect on the current section.  */

static int parse_section_arguments(char *c, int *size, int *blocking_flag, int *alignment_flag)
{
  if (c == ',')
    ++input_line_pointer;
  else
    {
      as_bad (_("Missing size argument"));
      ignore_rest_of_line ();
      return 0;
    }

  *size = get_absolute_expression ();
  *blocking_flag = 0;
  *alignment_flag = 0;

  if (*input_line_pointer == ',')
    {
      ++input_line_pointer;
      if (*input_line_pointer != ',')
        *blocking_flag = get_absolute_expression ();

      if (*input_line_pointer == ',')
        {
          ++input_line_pointer;
          *alignment_flag = get_absolute_expression ();
        }
    }

  return 1;
}

static void setup_line_label(segT seg)
{
  if (line_label == NULL)
    return;

  S_SET_SEGMENT (line_label, seg);
  symbol_set_frag (line_label, frag_now);
  S_SET_VALUE (line_label, frag_now_fix ());
  
  if (S_GET_STORAGE_CLASS (line_label) != C_EXT)
    S_SET_STORAGE_CLASS (line_label, C_LABEL);
}

static void apply_alignment(int alignment_flag)
{
  if (!alignment_flag)
    return;

  s_align_bytes (4);
  --input_line_pointer;
}

static flagword compute_section_flags(segT seg, int blocking_flag)
{
  flagword flags = bfd_section_flags (seg) | SEC_ALLOC;
  
  if (blocking_flag)
    flags |= SEC_TIC54X_BLOCK;
  
  return flags;
}

static void
tic54x_usect (int x ATTRIBUTE_UNUSED)
{
  char c;
  char *name;
  char *section_name;
  char *p;
  segT seg;
  int size, blocking_flag, alignment_flag;
  segT current_seg;
  subsegT current_subseg;
  flagword flags;

  ILLEGAL_WITHIN_STRUCT ();

  current_seg = now_seg;
  current_subseg = now_subseg;

  c = get_symbol_name (&section_name);
  name = xstrdup (section_name);
  c = restore_line_pointer (c);
  
  if (!parse_section_arguments(c, &size, &blocking_flag, &alignment_flag))
    return;

  seg = subseg_new (name, 0);
  
  apply_alignment(alignment_flag);
  setup_line_label(seg);
  
  seg_info (seg)->bss = 1;

  p = frag_var (rs_fill, 1, 1, 0, line_label, size * OCTETS_PER_BYTE, NULL);
  *p = 0;

  flags = compute_section_flags(seg, blocking_flag);

  if (!bfd_set_section_flags (seg, flags))
    as_warn (_("Error setting flags for \"%s\": %s"), name,
	     bfd_errmsg (bfd_get_error ()));

  subseg_set (current_seg, current_subseg);
  demand_empty_rest_of_line ();
}

static enum cpu_version
lookup_version (const char *ver)
{
  enum cpu_version version = VNONE;

  if (!is_version_54_prefix(ver))
    return version;

  if (is_three_char_version(ver))
    version = get_single_digit_version(ver[2]);
  else if (is_lp_version(ver))
    version = get_lp_version(ver[2]);

  return version;
}

static int
is_version_54_prefix(const char *ver)
{
  return ver[0] == '5' && ver[1] == '4';
}

static int
is_three_char_version(const char *ver)
{
  return strlen(ver) == 3 && is_valid_single_digit(ver[2]);
}

static int
is_valid_single_digit(char c)
{
  return c == '1' || c == '2' || c == '3' 
      || c == '5' || c == '8' || c == '9';
}

static enum cpu_version
get_single_digit_version(char c)
{
  return c - '0';
}

static int
is_lp_version(const char *ver)
{
  #define LP_VERSION_LENGTH 5
  #define LP_SUFFIX_POS_L 3
  #define LP_SUFFIX_POS_P 4
  
  return strlen(ver) == LP_VERSION_LENGTH
      && TOUPPER(ver[LP_SUFFIX_POS_L]) == 'L'
      && TOUPPER(ver[LP_SUFFIX_POS_P]) == 'P'
      && is_valid_lp_digit(ver[2]);
}

static int
is_valid_lp_digit(char c)
{
  return c == '5' || c == '6';
}

static enum cpu_version
get_lp_version(char c)
{
  #define LP_VERSION_OFFSET 10
  return c - '0' + LP_VERSION_OFFSET;
}

static void
set_cpu (enum cpu_version version)
{
  cpu = version;
  if (version == V545LP || version == V546LP)
    {
      create_allow_lp_symbol();
    }
}

static void
create_allow_lp_symbol(void)
{
  symbolS *symbolP = symbol_new ("__allow_lp", absolute_section,
                                 &zero_address_frag, 1);
  SF_SET_LOCAL (symbolP);
  symbol_table_insert (symbolP);
}

/* .version cpu-version
   cpu-version may be one of the following:
   541
   542
   543
   545
   545LP
   546LP
   548
   549

   This is for compatibility only.  It currently has no affect on assembly.  */
static int cpu_needs_set = 1;

static void
tic54x_version (int x ATTRIBUTE_UNUSED)
{
  enum cpu_version version = VNONE;
  enum cpu_version old_version = cpu;
  int c;
  char *ver;

  ILLEGAL_WITHIN_STRUCT ();

  SKIP_WHITESPACE ();
  ver = input_line_pointer;
  while (!is_end_of_stmt (*input_line_pointer))
    ++input_line_pointer;
  c = *input_line_pointer;
  *input_line_pointer = 0;

  version = lookup_version (ver);
  *input_line_pointer = c;

  if (version == VNONE)
    {
      as_bad (_("Unrecognized version '%s'"), ver);
      ignore_rest_of_line ();
      return;
    }

  if (cpu != VNONE && cpu != version)
    as_warn (_("CPU version has already been set"));

  if (assembly_begun && version != old_version)
    {
      as_bad (_("Changing of CPU version on the fly not supported"));
      ignore_rest_of_line ();
      return;
    }

  set_cpu (version);
  demand_empty_rest_of_line ();
}

/* 'f' = float, 'x' = xfloat, 'd' = double, 'l' = ldouble.  */

static void align_to_long_word_boundary(void)
{
    frag_align(2, 0, 2);
}

static void assign_label_to_current_position(void)
{
    if (line_label != NULL)
    {
        symbol_set_frag(line_label, frag_now);
        S_SET_VALUE(line_label, frag_now_fix());
    }
}

static void handle_float_alignment(int type)
{
    if (type != 'x')
    {
        align_to_long_word_boundary();
        assign_label_to_current_position();
    }
}

static void
tic54x_float_cons(int type)
{
    if (current_stag != 0)
        tic54x_struct_field('f');

#ifdef md_flush_pending_output
    md_flush_pending_output();
#endif

    handle_float_alignment(type);
    float_cons('f');
}

/* The argument is capitalized if it should be zero-terminated
   's' is normal string with upper 8-bits zero-filled, 'p' is packed.
   Code copied from stringer, and slightly modified so that strings are packed
   and encoded into the correct octets.  */

static void append_word(unsigned short value)
{
    FRAG_APPEND_1_CHAR(value & 0xFF);
    FRAG_APPEND_1_CHAR((value >> 8) & 0xFF);
}

static void append_packed_chars(int c, int *last_char)
{
    if (*last_char == -1)
    {
        *last_char = c;
    }
    else
    {
        FRAG_APPEND_1_CHAR(c);
        FRAG_APPEND_1_CHAR(*last_char);
        *last_char = -1;
    }
}

static void append_unpacked_char(int c)
{
    FRAG_APPEND_1_CHAR(c);
    FRAG_APPEND_1_CHAR(0);
}

static void append_terminator(int packed, int *last_char)
{
    if (packed && *last_char != -1)
    {
        FRAG_APPEND_1_CHAR(0);
        FRAG_APPEND_1_CHAR(*last_char);
        *last_char = -1;
    }
    else
    {
        FRAG_APPEND_1_CHAR(0);
        FRAG_APPEND_1_CHAR(0);
    }
}

static void process_string(int packed, int append_zero, int *last_char)
{
    int c;
    ++input_line_pointer;
    
    while (is_a_char(c = next_char_of_string()))
    {
        if (!packed)
        {
            append_unpacked_char(c);
        }
        else
        {
            append_packed_chars(c, last_char);
        }
    }
    
    if (append_zero)
    {
        append_terminator(packed, last_char);
    }
    
    know(input_line_pointer[-1] == '\"');
}

static void process_expression(void)
{
    unsigned short value = get_absolute_expression();
    append_word(value);
}

static void
tic54x_stringer(int type)
{
    unsigned int c;
    int append_zero = type == 'S' || type == 'P';
    int packed = type == 'p' || type == 'P';
    int last_char = -1;

    if (current_stag != NULL)
    {
        tic54x_struct_field('*');
        return;
    }

#ifdef md_flush_pending_output
    md_flush_pending_output();
#endif

    c = ',';
    while (c == ',')
    {
        SKIP_WHITESPACE();
        
        if (*input_line_pointer == '\"')
        {
            process_string(packed, append_zero, &last_char);
        }
        else
        {
            process_expression();
        }
        
        SKIP_WHITESPACE();
        c = *input_line_pointer;
        if (!is_end_of_stmt(c))
            ++input_line_pointer;
    }

    if (packed && last_char != -1)
    {
        FRAG_APPEND_1_CHAR(0);
        FRAG_APPEND_1_CHAR(last_char);
    }
    
    demand_empty_rest_of_line();
}

static void
tic54x_p2align (int arg ATTRIBUTE_UNUSED)
{
  as_bad (_("p2align not supported on this target"));
}

static int get_alignment_count(int arg)
{
    if (is_end_of_stmt(*input_line_pointer))
        return arg;
    
    if (arg == 2)
        as_warn(_("Argument to .even ignored"));
    else
        return get_absolute_expression();
    
    return arg;
}

static void handle_struct_alignment(void)
{
    if (current_stag->current_bitfield_offset != 0)
    {
        current_stag->current_bitfield_offset = 0;
        ++abs_section_offset;
    }
    demand_empty_rest_of_line();
}

static void tic54x_align_words(int arg)
{
    int count = get_alignment_count(arg);
    
    if (current_stag != NULL && arg == 128)
    {
        handle_struct_alignment();
        return;
    }
    
    ILLEGAL_WITHIN_STRUCT();
    s_align_bytes(count << 1);
}

/* Initialize multiple-bit fields within a single word of memory.  */

static int validate_field_size(int size)
{
  if (size < 1 || size > 32)
    {
      as_bad (_("Invalid field size, must be from 1 to 32"));
      ignore_rest_of_line ();
      return 0;
    }
  return 1;
}

static int validate_relocatable_field(int size)
{
  if (size != 16)
    {
      as_bad (_("field size must be 16 when value is relocatable"));
      ignore_rest_of_line ();
      return 0;
    }
  return 1;
}

static void emit_relocatable_field(expressionS *expn)
{
  frag_now->tc_frag_data = 0;
  emit_expr (expn, 2);
}

static valueT truncate_field_value(expressionS *expn, int size)
{
  #define FULL_32BIT_MASK 0xFFFFFFFF
  #define WORD_MASK 0xFFFF
  
  unsigned long fmask = (size == 32) ? FULL_32BIT_MASK : (1ul << size) - 1;
  valueT value = expn->X_add_number;
  
  expn->X_add_number &= fmask;
  if (value != (valueT) expn->X_add_number)
    as_warn (_("field value truncated"));
  
  return expn->X_add_number;
}

static void emit_full_words(valueT value, int *size)
{
  #define WORD_SIZE 16
  #define WORD_BYTES 2
  
  char *p;
  while (*size >= WORD_SIZE)
    {
      frag_now->tc_frag_data = 0;
      p = frag_more (WORD_BYTES);
      md_number_to_chars (p, (value >> (*size - WORD_SIZE)) & WORD_MASK, WORD_BYTES);
      *size -= WORD_SIZE;
    }
}

static struct bit_info* create_bit_info(valueT value, int size)
{
  struct bit_info *bi = XNEW (struct bit_info);
  expressionS size_exp;
  
  size_exp.X_op = O_constant;
  size_exp.X_add_number = size;
  bi->seg = now_seg;
  bi->type = TYPE_FIELD;
  bi->value = value;
  
  frag_var (rs_machine_dependent, 4, 1, 0,
            make_expr_symbol (&size_exp), 0, (char *) bi);
  return bi;
}

static char* get_field_position(fragS *alloc_frag, int bit_offset, int size)
{
  #define WORD_BITS 16
  #define WORD_BYTES 2
  
  char *p;
  
  if (bit_offset == 0 || bit_offset + size > WORD_BITS)
    {
      p = frag_more (WORD_BYTES);
      frag_now->tc_frag_data = 0;
    }
  else
    {
      p = alloc_frag == frag_now ?
          frag_now->fr_literal + frag_now_fix_octets () - WORD_BYTES :
          alloc_frag->fr_literal;
    }
  
  return p;
}

static void update_label_if_needed(symbolS *label, fragS *alloc_frag, int bit_offset, int size)
{
  if (label != NULL && !(bit_offset == 0 || bit_offset + size > 16))
    {
      symbol_set_frag (label, alloc_frag);
      if (alloc_frag == frag_now)
        S_SET_VALUE (label, frag_now_fix () - 1);
    }
}

static void write_partial_field(char *p, valueT value, fragS *alloc_frag, int size)
{
  #define WORD_BITS 16
  #define WORD_BYTES 2
  
  value <<= WORD_BITS - alloc_frag->tc_frag_data - size;
  
  if (alloc_frag->tc_frag_data)
    value |= ((uint16_t) p[1] << 8) | p[0];
  
  md_number_to_chars (p, value, WORD_BYTES);
  alloc_frag->tc_frag_data += size;
  
  if (alloc_frag->tc_frag_data == WORD_BITS)
    alloc_frag->tc_frag_data = 0;
}

static void emit_partial_field(valueT value, int size, symbolS *label)
{
  int bit_offset = frag_bit_offset (frag_now, now_seg);
  fragS *alloc_frag = bit_offset_frag (frag_now, now_seg);
  
  if (bit_offset == -1)
    {
      create_bit_info(value, size);
      return;
    }
  
  char *p = get_field_position(alloc_frag, bit_offset, size);
  
  if (bit_offset == 0 || bit_offset + size > 16)
    alloc_frag = frag_now;
  
  update_label_if_needed(label, alloc_frag, bit_offset, size);
  write_partial_field(p, value, alloc_frag, size);
}

static void process_constant_field(expressionS *expn, int size, symbolS *label)
{
  valueT value = truncate_field_value(expn, size);
  emit_full_words(value, &size);
  
  if (size > 0)
    emit_partial_field(value, size, label);
}

static void
tic54x_field (int ignore ATTRIBUTE_UNUSED)
{
  #define DEFAULT_FIELD_SIZE 16
  
  expressionS expn;
  int size = DEFAULT_FIELD_SIZE;
  symbolS *label = line_label;
  
  if (current_stag != NULL)
    {
      tic54x_struct_field ('.');
      return;
    }
  
  input_line_pointer = parse_expression (input_line_pointer, &expn);
  
  if (*input_line_pointer == ',')
    {
      ++input_line_pointer;
      size = get_absolute_expression ();
      if (!validate_field_size(size))
        return;
    }
  
  if (expn.X_op != O_constant)
    {
      if (!validate_relocatable_field(size))
        return;
      emit_relocatable_field(&expn);
    }
  else
    {
      process_constant_field(&expn, size, label);
    }
  
  demand_empty_rest_of_line ();
}

/* Ideally, we want to check SEC_LOAD and SEC_HAS_CONTENTS, but those aren't
   available yet.  seg_info ()->bss is the next best thing.  */

static int
tic54x_initialized_section (segT seg)
{
  return !seg_info (seg)->bss;
}

/* .clink ["section name"]

   Marks the section as conditionally linked (link only if contents are
   referenced elsewhere.
   Without a name, refers to the current initialized section.
   Name is required for uninitialized sections.  */

static char* extract_quoted_section_name(void)
{
    char *section_name = ++input_line_pointer;
    
    while (is_a_char(next_char_of_string()))
        ;
    
    know(input_line_pointer[-1] == '\"');
    input_line_pointer[-1] = 0;
    
    return xstrdup(section_name);
}

static segT get_section_by_name(const char *name)
{
    segT seg = bfd_get_section_by_name(stdoutput, name);
    
    if (seg == NULL)
    {
        as_bad(_("Unrecognized section '%s'"), name);
        ignore_rest_of_line();
    }
    
    return seg;
}

static int validate_current_section(segT seg)
{
    if (!tic54x_initialized_section(seg))
    {
        as_bad(_("Current section is uninitialized, "
                "section name required for .clink"));
        ignore_rest_of_line();
        return 0;
    }
    
    return 1;
}

static segT get_target_section(segT current_seg)
{
    if (*input_line_pointer == '\"')
    {
        char *name = extract_quoted_section_name();
        segT seg = get_section_by_name(name);
        free(name);
        return seg;
    }
    
    if (!validate_current_section(current_seg))
        return NULL;
    
    return current_seg;
}

static void
tic54x_clink(int ignored ATTRIBUTE_UNUSED)
{
    segT seg = now_seg;
    
    ILLEGAL_WITHIN_STRUCT();
    
    seg = get_target_section(seg);
    if (seg == NULL)
        return;
    
    seg->flags |= SEC_TIC54X_CLINK;
    demand_empty_rest_of_line();
}

/* Change the default include directory to be the current source file's
   directory.  */

static void
tic54x_set_default_include (void)
{
  unsigned lineno;
  const char *curfile = as_where (&lineno);
  const char *tmp = strrchr (curfile, '/');
  
  if (tmp == NULL)
    {
      include_dirs[0] = ".";
      return;
    }
  
  size_t len = tmp - curfile;
  if (len > include_dir_maxlen)
    include_dir_maxlen = len;
  include_dirs[0] = notes_memdup (curfile, len, len + 1);
}

/* .include "filename" | filename
   .copy    "filename" | filename

   FIXME 'include' file should be omitted from any output listing,
     'copy' should be included in any output listing
   FIXME -- prevent any included files from changing listing (compat only)
   FIXME -- need to include source file directory in search path; what's a
      good way to do this?

   Entering/exiting included/copied file clears all local labels.  */

static char* extract_quoted_filename(int *len)
{
    char *filename = demand_copy_C_string(len);
    demand_empty_rest_of_line();
    return filename;
}

static char* extract_unquoted_filename(void)
{
    char *filename = input_line_pointer;
    while (!is_end_of_stmt(*input_line_pointer))
        ++input_line_pointer;
    
    int c = *input_line_pointer;
    *input_line_pointer = '\0';
    char *result = xstrdup(filename);
    *input_line_pointer = c;
    demand_empty_rest_of_line();
    return result;
}

static char* get_include_filename(void)
{
    int len;
    
    if (*input_line_pointer == '"')
        return extract_quoted_filename(&len);
    else
        return extract_unquoted_filename();
}

static void insert_include_directive(char *filename)
{
    char newblock[] = " .newblock\n";
    char *input = concat("\"", filename, "\"\n", newblock, (char *) NULL);
    input_scrub_insert_line(input);
}

static void tic54x_include(int ignored ATTRIBUTE_UNUSED)
{
    ILLEGAL_WITHIN_STRUCT();
    SKIP_WHITESPACE();
    
    char *filename = get_include_filename();
    insert_include_directive(filename);
    
    tic54x_clear_local_labels(0);
    tic54x_set_default_include();
    s_include(0);
}

static char* extract_message(int *len)
{
    if (*input_line_pointer == '"')
        return demand_copy_C_string(len);
    
    char *msg = input_line_pointer;
    while (!is_end_of_stmt(*input_line_pointer))
        ++input_line_pointer;
    
    char c = *input_line_pointer;
    *input_line_pointer = 0;
    char *result = xstrdup(msg);
    *input_line_pointer = c;
    
    return result;
}

static void output_message(int type, char *msg)
{
    switch (type)
    {
    case 'm':
        as_tsktsk("%s", msg);
        break;
    case 'w':
        as_warn("%s", msg);
        break;
    case 'e':
        as_bad("%s", msg);
        break;
    }
}

static void tic54x_message(int type)
{
    ILLEGAL_WITHIN_STRUCT();
    
    int len;
    char *msg = extract_message(&len);
    
    output_message(type, msg);
    
    demand_empty_rest_of_line();
}

/* .label <symbol>
   Define a special symbol that refers to the loadtime address rather than the
   runtime address within the current section.

   This symbol gets a special storage class so that when it is resolved, it is
   resolved relative to the load address (lma) of the section rather than the
   run address (vma).  */

static void
tic54x_label (int ignored ATTRIBUTE_UNUSED)
{
  ILLEGAL_WITHIN_STRUCT ();

  char *name;
  int c = get_symbol_name (&name);
  
  symbolS *symbolP = colon (name);
  S_SET_STORAGE_CLASS (symbolP, C_STATLAB);

  restore_line_pointer (c);
  demand_empty_rest_of_line ();
}

/* .mmregs
   Install all memory-mapped register names into the symbol table as
   absolute local symbols.  */

static void
tic54x_register_mmregs (int ignored ATTRIBUTE_UNUSED)
{
  const tic54x_symbol *sym;

  ILLEGAL_WITHIN_STRUCT ();

  for (sym = tic54x_mmregs; sym->name; sym++)
    {
      symbolS *symbolP = symbol_new (sym->name, absolute_section,
				     &zero_address_frag, sym->value);
      SF_SET_LOCAL (symbolP);
      symbol_table_insert (symbolP);
    }
}

/* .loop [count]
   Count defaults to 1024.  */

static void
tic54x_loop (int count)
{
  ILLEGAL_WITHIN_STRUCT ();

  SKIP_WHITESPACE ();
  if (!is_end_of_stmt (*input_line_pointer))
    count = get_absolute_expression ();

  do_repeat ((size_t) count, "LOOP", "ENDLOOP", NULL);
}

/* Normally, endloop gets eaten by the preceding loop.  */

static void
tic54x_endloop (int ignore ATTRIBUTE_UNUSED)
{
  as_bad (_("ENDLOOP without corresponding LOOP"));
  ignore_rest_of_line ();
}

/* .break [condition].  */

static void
tic54x_break (int ignore ATTRIBUTE_UNUSED)
{
  ILLEGAL_WITHIN_STRUCT ();

  SKIP_WHITESPACE ();
  
  int cond = is_end_of_stmt (*input_line_pointer) ? 1 : get_absolute_expression ();

  if (cond)
    end_repeat (substitution_line ? 1 : 0);
}

static void
set_address_mode (int mode)
{
  amode = mode;
  if (mode == far_mode)
    {
      create_far_mode_symbol();
    }
}

static void
create_far_mode_symbol(void)
{
  const char *FAR_MODE_SYMBOL_NAME = "__allow_far";
  const valueT SYMBOL_VALUE = 1;
  
  symbolS *symbolP = symbol_new (FAR_MODE_SYMBOL_NAME, absolute_section,
                                &zero_address_frag, SYMBOL_VALUE);
  SF_SET_LOCAL (symbolP);
  symbol_table_insert (symbolP);
}

static int address_mode_needs_set = 1;

static void
tic54x_address_mode (int mode)
{
  if (is_invalid_address_mode_mix(mode))
    {
      as_bad (_("Mixing of normal and extended addressing not supported"));
      ignore_rest_of_line ();
      return;
    }
  
  if (is_extended_mode_unsupported(mode))
    {
      as_bad (_("Extended addressing not supported on the specified CPU"));
      ignore_rest_of_line ();
      return;
    }

  set_address_mode (mode);
  demand_empty_rest_of_line ();
}

static int
is_invalid_address_mode_mix(int mode)
{
  return assembly_begun && amode != (unsigned) mode;
}

static int
is_extended_mode_unsupported(int mode)
{
  return mode == far_mode && cpu != VNONE && cpu != V548 && cpu != V549;
}

/* .sblock "section"|section [,...,"section"|section]
   Designate initialized sections for blocking.  */

static char* get_section_name(void)
{
    if (*input_line_pointer == '"')
    {
        int len;
        return demand_copy_C_string(&len);
    }
    
    char *section_name;
    int c = get_symbol_name(&section_name);
    char *name = xstrdup(section_name);
    (void) restore_line_pointer(c);
    return name;
}

static segT validate_section(const char *name)
{
    segT seg = bfd_get_section_by_name(stdoutput, name);
    
    if (seg == NULL)
    {
        as_bad(_("Unrecognized section '%s'"), name);
        return NULL;
    }
    
    if (!tic54x_initialized_section(seg))
    {
        as_bad(_(".sblock may be used for initialized sections only"));
        return NULL;
    }
    
    return seg;
}

static int process_single_section(void)
{
    char *name = get_section_name();
    segT seg = validate_section(name);
    
    if (seg == NULL)
    {
        ignore_rest_of_line();
        return 0;
    }
    
    seg->flags |= SEC_TIC54X_BLOCK;
    
    int c = *input_line_pointer;
    if (!is_end_of_stmt(c))
        ++input_line_pointer;
    
    return c;
}

static void
tic54x_sblock (int ignore ATTRIBUTE_UNUSED)
{
    ILLEGAL_WITHIN_STRUCT();
    
    int c = ',';
    while (c == ',')
    {
        c = process_single_section();
        if (c == 0)
            return;
    }
    
    demand_empty_rest_of_line();
}

/* symbol .set value
   symbol .equ value

   value must be defined externals; no forward-referencing allowed
   symbols assigned with .set/.equ may not be redefined.  */

static symbolS* find_or_create_symbol(char *name)
{
    symbolS *symbolP = symbol_find(name);
    if (symbolP == NULL)
    {
        symbolP = md_undefined_symbol(name);
    }
    if (symbolP == NULL)
    {
        symbolP = symbol_new(name, absolute_section, &zero_address_frag, 0);
        S_SET_STORAGE_CLASS(symbolP, C_STAT);
    }
    return symbolP;
}

static void setup_symbol(symbolS *symbolP)
{
    S_SET_DATA_TYPE(symbolP, T_INT);
    S_SET_SEGMENT(symbolP, absolute_section);
    symbol_table_insert(symbolP);
    pseudo_set(symbolP);
}

static void tic54x_set(int ignore ATTRIBUTE_UNUSED)
{
    ILLEGAL_WITHIN_STRUCT();

    if (!line_label)
    {
        as_bad(_("Symbol missing for .set/.equ"));
        ignore_rest_of_line();
        return;
    }

    char *name = xstrdup(S_GET_NAME(line_label));
    line_label = NULL;
    
    symbolS *symbolP = find_or_create_symbol(name);
    free(name);
    
    setup_symbol(symbolP);
    demand_empty_rest_of_line();
}

/* .fclist
   .fcnolist
   List false conditional blocks.  */

static void
tic54x_fclist (int show)
{
  if (show)
    listing &= ~LISTING_NOCOND;
  else
    listing |= LISTING_NOCOND;
  demand_empty_rest_of_line ();
}

static void
tic54x_sslist (int show)
{
  ILLEGAL_WITHIN_STRUCT ();
  listing_sslist = show;
}

/* .var SYM[,...,SYMN]
   Define a substitution string to be local to a macro.  */

static int validate_macro_context(void)
{
    if (macro_level == 0)
    {
        as_bad(_(".var may only be used within a macro definition"));
        ignore_rest_of_line();
        return 0;
    }
    return 1;
}

static int validate_symbol_name(void)
{
    if (!ISALPHA(*input_line_pointer))
    {
        as_bad(_("Substitution symbols must begin with a letter"));
        ignore_rest_of_line();
        return 0;
    }
    return 1;
}

static subsym_ent_t* create_var_entry(void)
{
    subsym_ent_t *ent = xmalloc(sizeof(*ent));
    ent->u.s = (char *)"";
    ent->freekey = 1;
    ent->freeval = 0;
    ent->isproc = 0;
    ent->ismath = 0;
    return ent;
}

static int process_single_var(void)
{
    char *name;
    int c;
    
    if (!validate_symbol_name())
        return -1;
    
    c = get_symbol_name(&name);
    name = xstrdup(name);
    c = restore_line_pointer(c);
    
    subsym_ent_t *ent = create_var_entry();
    str_hash_insert(subsym_hash[macro_level], name, ent, 0);
    
    if (c == ',')
    {
        ++input_line_pointer;
        if (is_end_of_stmt(*input_line_pointer))
            c = *input_line_pointer;
    }
    
    return c;
}

static void
tic54x_var(int ignore ATTRIBUTE_UNUSED)
{
    int c;
    
    ILLEGAL_WITHIN_STRUCT();
    
    if (!validate_macro_context())
        return;
    
    do
    {
        c = process_single_var();
        if (c == -1)
            return;
    }
    while (c == ',');
    
    demand_empty_rest_of_line();
}

/* .mlib <macro library filename>

   Macro libraries are archived (standard AR-format) text macro definitions
   Expand the file and include it.

   FIXME need to try the source file directory as well.  */

static char* parse_quoted_filename(int *len)
{
    return demand_copy_C_string(len);
}

static char* parse_unquoted_filename(int *len)
{
    SKIP_WHITESPACE();
    *len = 0;
    while (!is_end_of_stmt(*input_line_pointer) && !is_whitespace(*input_line_pointer))
    {
        obstack_1grow(&notes, *input_line_pointer);
        ++input_line_pointer;
        ++(*len);
    }
    obstack_1grow(&notes, '\0');
    return obstack_finish(&notes);
}

static char* parse_filename(int *len)
{
    if (*input_line_pointer == '"')
        return parse_quoted_filename(len);
    return parse_unquoted_filename(len);
}

static char* find_library_path(const char *filename, int len)
{
    tic54x_set_default_include();
    char *path = notes_alloc(len + include_dir_maxlen + 2);
    FILE *try = search_and_open(filename, path);
    if (try)
        fclose(try);
    register_dependency(path);
    return path;
}

static bfd* open_archive(const char *path)
{
    bfd *abfd = bfd_openr(path, NULL);
    if (!abfd)
    {
        as_bad(_("can't open macro library file '%s' for reading: %s"),
               path, bfd_errmsg(bfd_get_error()));
        ignore_rest_of_line();
        return NULL;
    }
    if (!bfd_check_format(abfd, bfd_archive))
    {
        as_bad(_("File '%s' not in macro archive format"), path);
        ignore_rest_of_line();
        return NULL;
    }
    return abfd;
}

static void write_member_to_temp(char *buf, bfd_size_type size)
{
    char *fname = tmpnam(NULL);
    FILE *ftmp = fopen(fname, "w+b");
    fwrite(buf, size, 1, ftmp);
    if (size == 0 || buf[size - 1] != '\n')
        fwrite("\n", 1, 1, ftmp);
    fclose(ftmp);
    input_scrub_insert_file(fname);
    remove(fname);
}

static void process_archive_member(bfd *mbfd)
{
    bfd_size_type size = bfd_get_size(mbfd);
    char *buf = XNEWVEC(char, size);
    size = bfd_read(buf, size, mbfd);
    write_member_to_temp(buf, size);
    free(buf);
}

static void process_archive_members(bfd *abfd)
{
    bfd *mbfd;
    for (mbfd = bfd_openr_next_archived_file(abfd, NULL);
         mbfd != NULL; 
         mbfd = bfd_openr_next_archived_file(abfd, mbfd))
    {
        process_archive_member(mbfd);
    }
}

static void tic54x_mlib(int ignore ATTRIBUTE_UNUSED)
{
    char *filename;
    char *path;
    int len;
    bfd *abfd;

    ILLEGAL_WITHIN_STRUCT();

    filename = parse_filename(&len);
    if (!filename)
        return;

    demand_empty_rest_of_line();

    path = find_library_path(filename, len);

    abfd = open_archive(path);
    if (!abfd)
        return;

    process_archive_members(abfd);
}

const pseudo_typeS md_pseudo_table[] =
{
  { "algebraic", s_ignore                 ,          0 },
  { "align"    , tic54x_align_words       ,        128 },
  { "ascii"    , tic54x_stringer          ,        'p' },
  { "asciz"    , tic54x_stringer          ,        'P' },
  { "even"     , tic54x_align_words       ,          2 },
  { "asg"      , tic54x_asg               ,          0 },
  { "eval"     , tic54x_eval              ,          0 },
  { "bss"      , tic54x_bss               ,          0 },
  { "byte"     , tic54x_cons              ,        'b' },
  { "ubyte"    , tic54x_cons              ,        'B' },
  { "char"     , tic54x_cons              ,        'c' },
  { "uchar"    , tic54x_cons              ,        'C' },
  { "clink"    , tic54x_clink             ,          0 },
  { "c_mode"   , tic54x_address_mode      ,     c_mode },
  { "copy"     , tic54x_include           ,        'c' },
  { "include"  , tic54x_include           ,        'i' },
  { "data"     , tic54x_sect              ,        'd' },
  { "double"   , tic54x_float_cons        ,        'd' },
  { "ldouble"  , tic54x_float_cons        ,        'l' },
  { "drlist"   , s_ignore                 ,          0 },
  { "drnolist" , s_ignore                 ,          0 },
  { "emsg"     , tic54x_message           ,        'e' },
  { "mmsg"     , tic54x_message           ,        'm' },
  { "wmsg"     , tic54x_message           ,        'w' },
  { "far_mode" , tic54x_address_mode      ,   far_mode },
  { "fclist"   , tic54x_fclist            ,          1 },
  { "fcnolist" , tic54x_fclist            ,          0 },
  { "field"    , tic54x_field             ,         -1 },
  { "float"    , tic54x_float_cons        ,        'f' },
  { "xfloat"   , tic54x_float_cons        ,        'x' },
  { "global"   , tic54x_global            ,        'g' },
  { "def"      , tic54x_global            ,        'd' },
  { "ref"      , tic54x_global            ,        'r' },
  { "half"     , tic54x_cons              ,        'h' },
  { "uhalf"    , tic54x_cons              ,        'H' },
  { "short"    , tic54x_cons              ,        's' },
  { "ushort"   , tic54x_cons              ,        'S' },
  { "if"       , s_if                     , (int) O_ne },
  { "elseif"   , s_elseif                 , (int) O_ne },
  { "else"     , s_else                   ,          0 },
  { "endif"    , s_endif                  ,          0 },
  { "int"      , tic54x_cons              ,        'i' },
  { "uint"     , tic54x_cons              ,        'I' },
  { "word"     , tic54x_cons              ,        'w' },
  { "uword"    , tic54x_cons              ,        'W' },
  { "label"    , tic54x_label             ,          0 }, /* Loadtime
                                                             address.  */
  { "length"   , s_ignore                 ,          0 },
  { "width"    , s_ignore                 ,          0 },
  { "long"     , tic54x_cons              ,        'l' },
  { "ulong"    , tic54x_cons              ,        'L' },
  { "xlong"    , tic54x_cons              ,        'x' },
  { "loop"     , tic54x_loop              ,       1024 },
  { "break"    , tic54x_break             ,          0 },
  { "endloop"  , tic54x_endloop           ,          0 },
  { "mlib"     , tic54x_mlib              ,          0 },
  { "mlist"    , s_ignore                 ,          0 },
  { "mnolist"  , s_ignore                 ,          0 },
  { "mmregs"   , tic54x_register_mmregs   ,          0 },
  { "newblock" , tic54x_clear_local_labels,          0 },
  { "option"   , s_ignore                 ,          0 },
  { "p2align"  , tic54x_p2align           ,          0 },
  { "sblock"   , tic54x_sblock            ,          0 },
  { "sect"     , tic54x_sect              ,        '*' },
  { "set"      , tic54x_set               ,          0 },
  { "equ"      , tic54x_set               ,          0 },
  { "space"    , tic54x_space             ,          0 },
  { "bes"      , tic54x_space             ,          1 },
  { "sslist"   , tic54x_sslist            ,          1 },
  { "ssnolist" , tic54x_sslist            ,          0 },
  { "string"   , tic54x_stringer          ,        's' },
  { "pstring"  , tic54x_stringer          ,        'p' },
  { "struct"   , tic54x_struct            ,          0 },
  { "tag"      , tic54x_tag               ,          0 },
  { "endstruct", tic54x_endstruct         ,          0 },
  { "tab"      , s_ignore                 ,          0 },
  { "text"     , tic54x_sect              ,        't' },
  { "union"    , tic54x_struct            ,          1 },
  { "endunion" , tic54x_endstruct         ,          1 },
  { "usect"    , tic54x_usect             ,          0 },
  { "var"      , tic54x_var               ,          0 },
  { "version"  , tic54x_version           ,          0 },
  {0           , 0                        ,          0 }
};

int
md_parse_option (int c, const char *arg)
{
  switch (c)
    {
    default:
      return 0;
    case OPTION_COFF_VERSION:
      handle_coff_version(arg);
      break;
    case OPTION_CPU_VERSION:
      handle_cpu_version(arg);
      break;
    case OPTION_ADDRESS_MODE:
      amode = far_mode;
      address_mode_needs_set = 1;
      break;
    case OPTION_STDERR_TO_FILE:
      handle_stderr_redirect(arg);
      break;
    }

  return 1;
}

static void
handle_coff_version(const char *arg)
{
  int version = atoi(arg);
  
  if (version != 0 && version != 1 && version != 2)
    as_fatal(_("Bad COFF version '%s'"), arg);
}

static void
handle_cpu_version(const char *arg)
{
  cpu = lookup_version(arg);
  cpu_needs_set = 1;
  if (cpu == VNONE)
    as_fatal(_("Bad CPU version '%s'"), arg);
}

static void
handle_stderr_redirect(const char *arg)
{
  FILE *fp = fopen(arg, "w+");
  
  if (fp == NULL)
    as_fatal(_("Can't redirect stderr to the file '%s'"), arg);
    
  fclose(fp);
  
  if (freopen(arg, "w+", stderr) == NULL)
    as_fatal(_("Can't redirect stderr to the file '%s'"), arg);
}

/* Create a "local" substitution string hash table for a new macro level
   Some docs imply that macros have to use .newblock in order to be able
   to re-use a local label.  We effectively do an automatic .newblock by
   deleting the local label hash between macro invocations.  */

void
tic54x_macro_start (void)
{
  if (++macro_level >= MAX_SUBSYM_HASH)
    {
      --macro_level;
      as_fatal (_("Macro nesting is too deep"));
      return;
    }
  subsym_hash[macro_level] = subsym_htab_create ();
  local_label_hash[macro_level] = local_label_htab_create ();
}

void
tic54x_macro_info (const macro_entry *macro)
{
  const formal_entry *entry;

  for (entry = macro->formals; entry; entry = entry->next)
    {
      insert_formal_arg_as_subsym(entry);
    }
}

static void
insert_formal_arg_as_subsym(const formal_entry *entry)
{
  char *name = xstrndup (entry->name.ptr, entry->name.len);
  subsym_ent_t *ent = create_subsym_entry(entry);
  str_hash_insert (subsym_hash[macro_level], name, ent, 0);
}

static subsym_ent_t *
create_subsym_entry(const formal_entry *entry)
{
  subsym_ent_t *ent = xmalloc (sizeof (*ent));
  ent->u.s = xstrndup (entry->actual.ptr, entry->actual.len);
  ent->freekey = 1;
  ent->freeval = 1;
  ent->isproc = 0;
  ent->ismath = 0;
  return ent;
}

/* Get rid of this macro's .var's, arguments, and local labels.  */

void
tic54x_macro_end (void)
{
  htab_delete (subsym_hash[macro_level]);
  subsym_hash[macro_level] = NULL;
  htab_delete (local_label_hash[macro_level]);
  local_label_hash[macro_level] = NULL;
  --macro_level;
}

static int
subsym_symlen (char *a, char *ignore ATTRIBUTE_UNUSED)
{
  return strlen (a);
}

/* Compare symbol A to string B.  */

static int subsym_symcmp(char *a, char *b)
{
    return strcmp(a, b);
}

/* Return the index of the first occurrence of B in A, or zero if none
   assumes b is an integer char value as a string.  Index is one-based.  */

static int subsym_firstch(char *a, char *b)
{
    int val = atoi(b);
    char *tmp = strchr(a, val);
    return tmp ? tmp - a + 1 : 0;
}

/* Similar to firstch, but returns index of last occurrence of B in A.  */

static int subsym_lastch(char *a, char *b)
{
    int val = atoi(b);
    char *tmp = strrchr(a, val);
    return tmp ? tmp - a + 1 : 0;
}

/* Returns 1 if string A is defined in the symbol table (NOT the substitution
   symbol table).  */

static int subsym_isdefed(char *a, char *ignore ATTRIBUTE_UNUSED)
{
    return symbol_find(a) != NULL;
}

/* Assign first member of comma-separated list B (e.g. "1,2,3") to the symbol
   A, or zero if B is a null string.  Both arguments *must* be substitution
   symbols, unsubstituted.  */

static int validate_list_symbol(char *list, subsym_ent_t **listv)
{
    if (!list)
        return 0;

    *listv = subsym_lookup(list, macro_level);
    if (!*listv || (*listv)->isproc)
    {
        as_bad(_("Undefined substitution symbol '%s'"), list);
        ignore_rest_of_line();
        return 0;
    }
    return 1;
}

static char* extract_first_element(char *source)
{
    char *elem = notes_strdup(source);
    char *ptr = elem;
    
    while (*ptr && *ptr != ',')
        ++ptr;
    *ptr++ = 0;
    
    return elem;
}

static void update_symbols(char *sym, char *elem, char *list, char *remaining)
{
    subsym_create_or_replace(sym, elem);
    subsym_create_or_replace(list, remaining);
}

static int subsym_ismember(char *sym, char *list)
{
    subsym_ent_t *listv;
    
    if (!validate_list_symbol(list, &listv))
        return 0;
    
    char *elem = extract_first_element(listv->u.s);
    char *ptr = elem + strlen(elem) + 1;
    
    update_symbols(sym, elem, list, ptr);
    
    return *list != 0;
}

/* Return zero if not a constant; otherwise:
   1 if binary
   2 if octal
   3 if hexadecimal
   4 if character
   5 if decimal.  */

static int get_suffix_type(char suffix)
{
    switch (TOUPPER(suffix))
    {
    case 'B':
        return 1;
    case 'Q':
        return 2;
    case 'H':
        return 3;
    case '\'':
        return 4;
    default:
        return 0;
    }
}

static int get_prefix_type(char *a, int len)
{
    #define HEX_PREFIX_TYPE 3
    #define OCTAL_PREFIX_TYPE 2
    #define DECIMAL_TYPE 5
    
    if (*a == '0' && len > 1)
    {
        if (TOUPPER(a[1]) == 'X')
            return HEX_PREFIX_TYPE;
        return OCTAL_PREFIX_TYPE;
    }
    return DECIMAL_TYPE;
}

static int
subsym_iscons (char *a, char *ignore ATTRIBUTE_UNUSED)
{
    expressionS expn;

    parse_expression(a, &expn);

    if (expn.X_op != O_constant)
        return 0;

    int len = strlen(a);
    int suffix_type = get_suffix_type(a[len - 1]);
    
    if (suffix_type != 0)
        return suffix_type;

    return get_prefix_type(a, len);
}

/* Return 1 if A is a valid symbol name.  Expects string input.   */

static int
subsym_isname (char *a, char *ignore ATTRIBUTE_UNUSED)
{
  if (!is_name_beginner (*a))
    return 0;
  
  while (*a)
    {
      if (!is_part_of_name (*a))
        return 0;
      ++a;
    }
  
  return 1;
}

/* Return whether the string is a register; accepts ar0-7, unless .mmregs has
   been seen; if so, recognize any memory-mapped register.
   Note this does not recognize "A" or "B" accumulators.  */

static int
subsym_isreg (char *a, char *ignore ATTRIBUTE_UNUSED)
{
  return str_hash_find (reg_hash, a) || str_hash_find (mmreg_hash, a);
}

/* Return the structure size, given the stag.  */

static int
subsym_structsz (char *name, char *ignore ATTRIBUTE_UNUSED)
{
  struct stag *stag = str_hash_find (stag_hash, name);
  return stag ? stag->size : 0;
}

/* If anybody actually uses this, they can fix it :)
   FIXME I'm not sure what the "reference point" of a structure is.  It might
   be either the initial offset given .struct, or it may be the offset of the
   structure within another structure, or it might be something else
   altogether.  since the TI assembler doesn't seem to ever do anything but
   return zero, we punt and return zero.  */

static int subsym_structacc(char *stag_name ATTRIBUTE_UNUSED, char *ignore ATTRIBUTE_UNUSED)
{
    return 0;
}

static float
math_ceil (float arg1, float ignore ATTRIBUTE_UNUSED)
{
  return (float) ceil (arg1);
}

static int
math_cvi(float arg1, float ignore ATTRIBUTE_UNUSED)
{
    return (int)arg1;
}

static float
math_floor (float arg1, float ignore ATTRIBUTE_UNUSED)
{
  return (float) floor (arg1);
}

static float
math_fmod (float arg1, float arg2)
{
  return (int) arg1 % (int) arg2;
}

static int
math_int (float arg1, float ignore ATTRIBUTE_UNUSED)
{
  return arg1 == (float) (int) arg1;
}

static float
math_round (float arg1, float ignore ATTRIBUTE_UNUSED)
{
  const float ROUNDING_OFFSET = 0.5;
  return arg1 > 0 ? (int) (arg1 + ROUNDING_OFFSET) : (int) (arg1 - ROUNDING_OFFSET);
}

static int
math_sgn (float arg1, float ignore ATTRIBUTE_UNUSED)
{
  if (arg1 < 0.0f) {
    return -1;
  }
  if (arg1 > 0.0f) {
    return 1;
  }
  return 0;
}

static float
math_trunc (float arg1, float ignore ATTRIBUTE_UNUSED)
{
  return (int) arg1;
}

static float
math_acos (float arg1, float ignore ATTRIBUTE_UNUSED)
{
  return (float) acos (arg1);
}

static float
math_asin (float arg1, float ignore ATTRIBUTE_UNUSED)
{
  return (float) asin (arg1);
}

static float
math_atan (float arg1, float ignore ATTRIBUTE_UNUSED)
{
  return (float) atan (arg1);
}

static float
math_atan2 (float arg1, float arg2)
{
  return (float) atan2 (arg1, arg2);
}

static float
math_cosh (float arg1, float ignore ATTRIBUTE_UNUSED)
{
  return (float) cosh (arg1);
}

static float
math_cos (float arg1, float ignore ATTRIBUTE_UNUSED)
{
  return (float) cos (arg1);
}

static float
math_cvf (float arg1, float ignore ATTRIBUTE_UNUSED)
{
  return (float) arg1;
}

static float
math_exp(float arg1, float ignore ATTRIBUTE_UNUSED)
{
    return (float)exp(arg1);
}

static float
math_fabs (float arg1, float ignore ATTRIBUTE_UNUSED)
{
  return (float) fabs (arg1);
}

/* expr1 * 2^expr2.  */

static float math_ldexp(float arg1, float arg2)
{
    const float BASE = 2.0;
    return arg1 * (float)pow(BASE, arg2);
}

static float
math_log10 (float arg1, float ignore ATTRIBUTE_UNUSED)
{
  return (float) log10 (arg1);
}

static float
math_log (float arg1, float ignore ATTRIBUTE_UNUSED)
{
  return (float) log (arg1);
}

static float
math_max (float arg1, float arg2)
{
  return (arg1 > arg2) ? arg1 : arg2;
}

static float
math_min (float arg1, float arg2)
{
  return (arg1 < arg2) ? arg1 : arg2;
}

static float
math_pow (float arg1, float arg2)
{
  return (float) pow (arg1, arg2);
}

static float
math_sin (float arg1, float ignore ATTRIBUTE_UNUSED)
{
  return (float) sin (arg1);
}

static float
math_sinh (float arg1, float ignore ATTRIBUTE_UNUSED)
{
  return (float) sinh (arg1);
}

static float
math_sqrt(float arg1, float ignore ATTRIBUTE_UNUSED)
{
    return (float)sqrt(arg1);
}

static float
math_tan (float arg1, float ignore ATTRIBUTE_UNUSED)
{
  return (float) tan (arg1);
}

static float
math_tanh (float arg1, float ignore ATTRIBUTE_UNUSED)
{
  return (float) tanh (arg1);
}

/* Built-in substitution symbol functions and math functions.  */
static const subsym_proc_entry subsym_procs[] =
{
  /* Assembler built-in string substitution functions.  */
  { "$symlen",    { .s = subsym_symlen },    1, 0 },
  { "$symcmp",    { .s = subsym_symcmp },    2, 0 },
  { "$firstch",   { .s = subsym_firstch },   2, 0 },
  { "$lastch",    { .s = subsym_lastch },    2, 0 },
  { "$isdefed",   { .s = subsym_isdefed },   1, 0 },
  { "$ismember",  { .s = subsym_ismember },  2, 0 },
  { "$iscons",    { .s = subsym_iscons },    1, 0 },
  { "$isname",    { .s = subsym_isname },    1, 0 },
  { "$isreg",     { .s = subsym_isreg },     1, 0 },
  { "$structsz",  { .s = subsym_structsz },  1, 0 },
  { "$structacc", { .s = subsym_structacc }, 1, 0 },

  /* Integer-returning built-in math functions.  */
  { "$cvi",       { .i = math_cvi },         1, 2 },
  { "$int",       { .i = math_int },         1, 2 },
  { "$sgn",       { .i = math_sgn },         1, 2 },

  /* Float-returning built-in math functions.  */
  { "$acos",      { .f = math_acos },        1, 1 },
  { "$asin",      { .f = math_asin },        1, 1 },
  { "$atan",      { .f = math_atan },        1, 1 },
  { "$atan2",     { .f = math_atan2 },       2, 1 },
  { "$ceil",      { .f = math_ceil },        1, 1 },
  { "$cosh",      { .f = math_cosh },        1, 1 },
  { "$cos",       { .f = math_cos },         1, 1 },
  { "$cvf",       { .f = math_cvf },         1, 1 },
  { "$exp",       { .f = math_exp },         1, 1 },
  { "$fabs",      { .f = math_fabs },        1, 1 },
  { "$floor",     { .f = math_floor },       1, 1 },
  { "$fmod",      { .f = math_fmod },        2, 1 },
  { "$ldexp",     { .f = math_ldexp },       2, 1 },
  { "$log10",     { .f = math_log10 },       1, 1 },
  { "$log",       { .f = math_log },         1, 1 },
  { "$max",       { .f = math_max },         2, 1 },
  { "$min",       { .f = math_min },         2, 1 },
  { "$pow",       { .f = math_pow },         2, 1 },
  { "$round",     { .f = math_round },       1, 1 },
  { "$sin",       { .f = math_sin },         1, 1 },
  { "$sinh",      { .f = math_sinh },        1, 1 },
  { "$sqrt",      { .f = math_sqrt },        1, 1 },
  { "$tan",       { .f = math_tan },         1, 1 },
  { "$tanh",      { .f = math_tanh },        1, 1 },
  { "$trunc",     { .f = math_trunc },       1, 1 },
  { NULL, { NULL }, 0, 0 },
};

void md_begin(void)
{
    local_label_id = 0;
    
    process_environment_directories();
    initialize_hash_tables();
    populate_instruction_tables();
    populate_register_tables();
    populate_condition_code_tables();
    populate_misc_tables();
    initialize_subsym_tables();
}

static void process_environment_directories(void)
{
    char *TIC54X_DIR = getenv("TIC54X_DIR");
    char *A_DIR = TIC54X_DIR ? TIC54X_DIR : getenv("A_DIR");
    
    if (A_DIR != NULL)
    {
        add_directories_from_path(A_DIR);
    }
}

static void add_directories_from_path(char *path)
{
    char *tmp = notes_strdup(path);
    char *current = tmp;
    
    while (current != NULL)
    {
        char *next = strchr(current, ';');
        if (next)
            *next++ = '\0';
        add_include_dir(current);
        current = next;
    }
}

static void initialize_hash_tables(void)
{
    op_hash = str_htab_create();
    parop_hash = str_htab_create();
    reg_hash = str_htab_create();
    mmreg_hash = str_htab_create();
    cc_hash = str_htab_create();
    cc2_hash = str_htab_create();
    cc3_hash = str_htab_create();
    sbit_hash = str_htab_create();
    misc_symbol_hash = str_htab_create();
    subsym_recurse_hash = str_htab_create();
    stag_hash = str_htab_create();
}

static void populate_instruction_tables(void)
{
    populate_template_hash(op_hash, (insn_template *)tic54x_optab);
    populate_template_hash(parop_hash, (insn_template *)tic54x_paroptab);
}

static void populate_template_hash(htab_t hash, insn_template *templates)
{
    insn_template *tm;
    for (tm = templates; tm->name; tm++)
        str_hash_insert(hash, tm->name, tm, 0);
}

static void populate_register_tables(void)
{
    populate_basic_registers();
    populate_mmregs();
}

static void populate_basic_registers(void)
{
    const tic54x_symbol *sym;
    for (sym = tic54x_regs; sym->name; sym++)
    {
        symbolS *symbolP = symbol_new(sym->name, absolute_section,
                                      &zero_address_frag, sym->value);
        SF_SET_LOCAL(symbolP);
        symbol_table_insert(symbolP);
        str_hash_insert(reg_hash, sym->name, sym, 0);
    }
}

static void populate_mmregs(void)
{
    const tic54x_symbol *sym;
    for (sym = tic54x_mmregs; sym->name; sym++)
    {
        str_hash_insert(reg_hash, sym->name, sym, 0);
        str_hash_insert(mmreg_hash, sym->name, sym, 0);
    }
}

static void populate_condition_code_tables(void)
{
    populate_symbol_hash(cc_hash, tic54x_condition_codes);
    populate_symbol_hash(cc2_hash, tic54x_cc2_codes);
    populate_symbol_hash(cc3_hash, tic54x_cc3_codes);
    populate_symbol_hash(sbit_hash, tic54x_status_bits);
}

static void populate_symbol_hash(htab_t hash, const tic54x_symbol *symbols)
{
    const tic54x_symbol *sym;
    for (sym = symbols; sym->name; sym++)
        str_hash_insert(hash, sym->name, sym, 0);
}

static void populate_misc_tables(void)
{
    const char **symname;
    for (symname = tic54x_misc_symbols; *symname; symname++)
        str_hash_insert(misc_symbol_hash, *symname, *symname, 0);
}

static void initialize_subsym_tables(void)
{
    local_label_hash[0] = local_label_htab_create();
    subsym_hash[0] = subsym_htab_create();
    populate_subsym_procedures();
}

static void populate_subsym_procedures(void)
{
    const subsym_proc_entry *subsym_proc;
    for (subsym_proc = subsym_procs; subsym_proc->name; subsym_proc++)
    {
        subsym_ent_t *ent = create_subsym_entry(subsym_proc);
        str_hash_insert(subsym_hash[0], subsym_proc->name, ent, 0);
    }
}

static subsym_ent_t *create_subsym_entry(const subsym_proc_entry *proc)
{
    subsym_ent_t *ent = xmalloc(sizeof(*ent));
    ent->u.p = proc;
    ent->freekey = 0;
    ent->freeval = 0;
    ent->isproc = 1;
    ent->ismath = proc->type != 0;
    return ent;
}

void
tic54x_md_end (void)
{
  delete_hash_tables();
  cleanup_macros();
}

static void
delete_hash_tables (void)
{
  htab_delete (stag_hash);
  htab_delete (subsym_recurse_hash);
  htab_delete (misc_symbol_hash);
  htab_delete (sbit_hash);
  htab_delete (cc3_hash);
  htab_delete (cc2_hash);
  htab_delete (cc_hash);
  htab_delete (mmreg_hash);
  htab_delete (reg_hash);
  htab_delete (parop_hash);
  htab_delete (op_hash);
}

static void
cleanup_macros (void)
{
  while (macro_level != -1)
    tic54x_macro_end ();
  macro_level = 0;
}

static int
is_accumulator (struct opstruct *operand)
{
  return strcasecmp (operand->buf, "a") == 0
    || strcasecmp (operand->buf, "b") == 0;
}

/* Return the number of operands found, or -1 on error, copying the
   operands into the given array and the accompanying expressions into
   the next array.  */

static void skip_whitespace(char **ptr)
{
    while (is_whitespace(**ptr))
        ++(*ptr);
}

static int check_parenthesis_balance(char **lptr, int *paren_count)
{
    if (**lptr == '(')
        ++(*paren_count);
    else if (**lptr == ')')
        --(*paren_count);
    ++(*lptr);
    return *paren_count;
}

static int find_operand_end(char **lptr, int *paren_not_balanced, int numexp)
{
    while (*paren_not_balanced || **lptr != ',')
    {
        if (**lptr == '\0')
        {
            if (*paren_not_balanced)
            {
                as_bad(_("Unbalanced parenthesis in operand %d"), numexp);
                return -1;
            }
            break;
        }
        check_parenthesis_balance(lptr, paren_not_balanced);
    }
    return 0;
}

static void copy_operand(struct opstruct *operand, char *op_start, int len)
{
    strncpy(operand->buf, op_start, len);
    operand->buf[len] = 0;
    while (len > 0 && is_whitespace(operand->buf[len - 1]))
        operand->buf[--len] = 0;
}

static int check_comma_syntax(char **lptr, int expecting_operand)
{
    if (**lptr == ',')
    {
        if (*++(*lptr) == '\0')
        {
            as_bad(_("Expecting operand after ','"));
            return -1;
        }
        return 1;
    }
    return expecting_operand;
}

static int extract_single_operand(struct opstruct *operand, char **lptr, int numexp, int *expecting_operand)
{
    int paren_not_balanced = 0;
    char *op_start, *op_end;
    
    skip_whitespace(lptr);
    op_start = *lptr;
    
    if (find_operand_end(lptr, &paren_not_balanced, numexp) < 0)
        return -1;
    
    op_end = *lptr;
    
    if (op_end != op_start)
    {
        int len = op_end - op_start;
        copy_operand(operand, op_start, len);
        *lptr = op_end;
        return 1;
    }
    
    if (*expecting_operand || **lptr == ',')
    {
        as_bad(_("Expecting operand after ','"));
        return -1;
    }
    
    return 0;
}

static int extract_operands(struct opstruct operands[], char *line)
{
    char *lptr = line;
    int numexp = 0;
    int expecting_operand = 0;
    
    while (numexp < MAX_OPERANDS && !is_end_of_stmt(*lptr))
    {
        int result = extract_single_operand(&operands[numexp], &lptr, numexp, &expecting_operand);
        if (result < 0)
            return -1;
        if (result > 0)
            ++numexp;
        
        int new_expecting = check_comma_syntax(&lptr, expecting_operand);
        if (new_expecting < 0)
            return -1;
        expecting_operand = new_expecting;
    }
    
    skip_whitespace(&lptr);
    if (!is_end_of_stmt(*lptr))
    {
        as_bad(_("Extra junk on line"));
        return -1;
    }
    
    return numexp;
}

static void parse_immediate_operand(struct opstruct *operand)
{
    parse_expression(operand->buf + 1, &operand->exp);
}

static void parse_direct_operand(struct opstruct *operand)
{
    parse_expression(operand->buf + 1, &operand->exp);
}

static int find_matching_paren(char *paren)
{
    int len = strlen(paren);
    char *end = paren + len;
    
    while (end[-1] != ')')
    {
        if (--end <= paren)
            return -1;
    }
    return end - paren;
}

static void parse_indirect_operand(struct opstruct *operand)
{
    char *paren = strchr(operand->buf, '(');
    
    if (paren && paren[1] == '#')
        *++paren = '(';
    
    if (paren != NULL)
    {
        int offset = find_matching_paren(paren);
        if (offset < 0)
        {
            as_bad(_("Badly formed address expression"));
            return;
        }
        char *end = paren + offset;
        int c = *end;
        *end = '\0';
        parse_expression(paren, &operand->exp);
        *end = c;
    }
    else
    {
        operand->exp.X_op = O_absent;
    }
}

#define IMMEDIATE_PREFIX '#'
#define DIRECT_PREFIX '@'
#define INDIRECT_PREFIX '*'

static void parse_operand_expression(struct opstruct *operand)
{
    memset(&operand->exp, 0, sizeof(operand->exp));
    
    if (operand->buf[0] == IMMEDIATE_PREFIX)
        parse_immediate_operand(operand);
    else if (operand->buf[0] == DIRECT_PREFIX)
        parse_direct_operand(operand);
    else if (operand->buf[0] == INDIRECT_PREFIX)
        parse_indirect_operand(operand);
    else
        parse_expression(operand->buf, &operand->exp);
}

static int get_operands(struct opstruct operands[], char *line)
{
    int numexp = extract_operands(operands, line);
    if (numexp < 0)
        return -1;
    
    for (int i = 0; i < numexp; i++)
        parse_operand_expression(&operands[i]);
    
    return numexp;
}

/* Predicates for different operand types.  */

static int is_immediate(struct opstruct *operand)
{
    const char IMMEDIATE_PREFIX = '#';
    return *operand->buf == IMMEDIATE_PREFIX;
}

/* This is distinguished from immediate because some numbers must be constants
   and must *not* have the '#' prefix.  */

static int
is_absolute (struct opstruct *operand)
{
  return operand->exp.X_op == O_constant && !is_immediate (operand);
}

/* Is this an indirect operand?  */

static int is_indirect(struct opstruct *operand)
{
    const char INDIRECT_OPERATOR = '*';
    return operand->buf[0] == INDIRECT_OPERATOR;
}

/* Is this a valid dual-memory operand?  */

static int is_ar_prefix(const char *buf)
{
    return strncasecmp(buf, "*ar", 3) == 0;
}

static int get_ar_index(const char *buf)
{
    return buf[3] - '0';
}

static int is_valid_ar_index(int index)
{
    return index >= 2 && index <= 5;
}

static int is_valid_ar_modifier(const char *modifier)
{
    return *modifier == '\0' ||
           strcasecmp(modifier, "-") == 0 ||
           strcasecmp(modifier, "+") == 0 ||
           strcasecmp(modifier, "+0%") == 0;
}

static int
is_dual(struct opstruct *operand)
{
    if (!is_indirect(operand) || !is_ar_prefix(operand->buf))
    {
        return 0;
    }
    
    int arf = get_ar_index(operand->buf);
    const char *modifier = operand->buf + 4;
    
    return is_valid_ar_index(arf) && is_valid_ar_modifier(modifier);
}

static int
is_mmreg(struct opstruct *operand)
{
    if (is_absolute(operand)) {
        return 1;
    }
    
    if (is_immediate(operand)) {
        return 1;
    }
    
    if (str_hash_find(mmreg_hash, operand->buf) != NULL) {
        return 1;
    }
    
    return 0;
}

#define SHIFT_RANGE_MIN 0
#define SHIFT_RANGE_MAX 16
#define K8U_MAX 256
#define AR_PREFIX_LEN 2

static int is_buffer_empty(struct opstruct *operand)
{
    return operand->buf[0] == 0;
}

static int is_accumulator_type(struct opstruct *operand, char type_char)
{
    return is_accumulator(operand) && TOUPPER(operand->buf[0]) == type_char;
}

static int is_arx_register(struct opstruct *operand)
{
    return strncasecmp("ar", operand->buf, AR_PREFIX_LEN) == 0
        && ISDIGIT(operand->buf[AR_PREFIX_LEN]);
}

static int is_hash_found(void *hash, struct opstruct *operand)
{
    return str_hash_find(hash, operand->buf) != 0;
}

static int is_immediate_or_absolute(struct opstruct *operand)
{
    return is_immediate(operand) || is_absolute(operand);
}

static int is_immediate_with_value(struct opstruct *operand, int value)
{
    return is_immediate_or_absolute(operand) 
        && operand->exp.X_add_number == value;
}

static int is_immediate_in_range(struct opstruct *operand, int min, int max)
{
    return is_immediate_or_absolute(operand)
        && operand->exp.X_add_number >= min 
        && operand->exp.X_add_number < max;
}

static int is_k8u_operand(struct opstruct *operand)
{
    return is_immediate(operand)
        && operand->exp.X_op == O_constant
        && operand->exp.X_add_number >= 0
        && operand->exp.X_add_number < K8U_MAX;
}

static int is_n_operand(struct opstruct *operand)
{
    return is_immediate_or_absolute(operand) ||
        strcasecmp("st0", operand->buf) == 0 ||
        strcasecmp("st1", operand->buf) == 0;
}

static int is_shift_not_16(struct opstruct *operand)
{
    return is_immediate_or_absolute(operand)
        && operand->exp.X_add_number != SHIFT_RANGE_MAX;
}

static int is_string_match(const char *str, struct opstruct *operand)
{
    return strcasecmp(str, operand->buf) == 0;
}

static int
is_type(struct opstruct *operand, enum optype type)
{
    switch (type)
    {
    case OP_None:
        return is_buffer_empty(operand);
    case OP_Xmem:
    case OP_Ymem:
        return is_dual(operand);
    case OP_Sind:
        return is_indirect(operand);
    case OP_xpmad_ms7:
        return is_immediate(operand);
    case OP_xpmad:
    case OP_pmad:
    case OP_PA:
    case OP_dmad:
    case OP_Lmem:
    case OP_MMR:
    case OP_lk:
    case OP_lku:
        return 1;
    case OP_Smem:
        return !is_immediate(operand);
    case OP_MMRY:
    case OP_MMRX:
        return is_mmreg(operand);
    case OP_SRC:
    case OP_SRC1:
    case OP_RND:
    case OP_DST:
        return is_accumulator(operand);
    case OP_B:
        return is_accumulator_type(operand, 'B');
    case OP_A:
        return is_accumulator_type(operand, 'A');
    case OP_ARX:
        return is_arx_register(operand);
    case OP_SBIT:
        return is_hash_found(sbit_hash, operand) || is_absolute(operand);
    case OP_CC:
        return is_hash_found(cc_hash, operand);
    case OP_CC2:
        return is_hash_found(cc2_hash, operand);
    case OP_CC3:
        return is_hash_found(cc3_hash, operand) || is_immediate_or_absolute(operand);
    case OP_16:
        return is_immediate_with_value(operand, SHIFT_RANGE_MAX);
    case OP_N:
        return is_n_operand(operand);
    case OP_12:
    case OP_123:
    case OP_BITC:
    case OP_031:
    case OP_k8:
        return is_immediate_or_absolute(operand);
    case OP_SHFT:
        return is_immediate_in_range(operand, SHIFT_RANGE_MIN, SHIFT_RANGE_MAX);
    case OP_SHIFT:
        return is_shift_not_16(operand);
    case OP_k8u:
        return is_k8u_operand(operand);
    case OP_k5:
    case OP_k3:
    case OP_k9:
        return is_immediate(operand);
    case OP_T:
        return is_string_match("t", operand) || is_string_match("treg", operand);
    case OP_TS:
        return is_string_match("ts", operand);
    case OP_ASM:
        return is_string_match("asm", operand);
    case OP_TRN:
        return is_string_match("trn", operand);
    case OP_DP:
        return is_string_match("dp", operand);
    case OP_ARP:
        return is_string_match("arp", operand);
    default:
        return 0;
    }
}

static int check_optional_operand(const enum optype *refoptype, int *refop, int *maxops)
{
    if (refoptype[*refop] & OPT)
    {
        ++(*refop);
        --(*maxops);
        return (*refop <= *maxops);
    }
    return 0;
}

static int process_remaining_operands(tic54x_insn *insn, const enum optype *refoptype, int *refop, int op, int maxops)
{
    while (op < maxops)
    {
        if ((refoptype[*refop] & OPT) == 0)
            return 0;
        
        if (OPTYPE(refoptype[*refop]) == OP_DST)
            insn->using_default_dst = 1;
        
        ++(*refop);
        ++op;
    }
    return 1;
}

static int find_matching_operand(struct opstruct *operands, const enum optype *refoptype, int op, int *refop, int *maxops)
{
    while (!is_type(&operands[op], OPTYPE(refoptype[*refop])))
    {
        if (!check_optional_operand(refoptype, refop, maxops))
            return 0;
    }
    
    operands[op].type = OPTYPE(refoptype[*refop]);
    return 1;
}

static int operands_match(tic54x_insn *insn,
                          struct opstruct *operands,
                          int opcount,
                          const enum optype *refoptype,
                          int minops,
                          int maxops)
{
    int op = 0, refop = 0;

    if (opcount == 0 && minops == 0)
        return 1;

    while (op <= maxops && refop <= maxops)
    {
        if (!find_matching_operand(operands, refoptype, op, &refop, &maxops))
            return 0;
        
        ++refop;
        ++op;
        
        if (op == opcount)
            return process_remaining_operands(insn, refoptype, &refop, op, maxops);
    }

    return 0;
}

/* 16-bit direct memory address
   Explicit dmad operands are always in last word of insn (usually second
   word, but bumped to third if lk addressing is used)

   We allow *(dmad) notation because the TI assembler allows it.

   XPC_CODE:
   0 for 16-bit addresses
   1 for full 23-bit addresses
   2 for the upper 7 bits of a 23-bit address (LDX).  */

static int validate_dmad_syntax(struct opstruct *operand)
{
    if (is_indirect(operand) && operand->buf[strlen(operand->buf) - 1] != ')')
    {
        as_bad(_("Invalid dmad syntax '%s'"), operand->buf);
        return 0;
    }
    return 1;
}

static void handle_constant_xpc_code_1(tic54x_insn *insn, valueT value)
{
    #define WORD0_MASK 0xFF80
    #define HIGH_BYTE_MASK 0x7F
    #define LOW_WORD_MASK 0xFFFF
    #define HIGH_WORD_SHIFT 16
    
    insn->opcode[0].word &= WORD0_MASK;
    insn->opcode[0].word |= (value >> HIGH_WORD_SHIFT) & HIGH_BYTE_MASK;
    insn->opcode[1].word = value & LOW_WORD_MASK;
}

static void handle_constant_xpc_code_2(tic54x_insn *insn, valueT value, int op)
{
    #define HIGH_WORD_SHIFT 16
    #define HIGH_WORD_MASK 0xFFFF
    
    insn->opcode[op].word = (value >> HIGH_WORD_SHIFT) & HIGH_WORD_MASK;
}

static void handle_constant_expression(tic54x_insn *insn, int op, int xpc_code)
{
    valueT value = insn->opcode[op].addr_expr.X_add_number;
    
    if (xpc_code == 1)
    {
        handle_constant_xpc_code_1(insn, value);
    }
    else if (xpc_code == 2)
    {
        handle_constant_xpc_code_2(insn, value, op);
    }
    else
    {
        insn->opcode[op].word = value;
    }
}

static void setup_xpc_code_1_relocation(tic54x_insn *insn, struct opstruct *operand)
{
    insn->opcode[0].addr_expr = operand->exp;
    insn->opcode[0].r_type = BFD_RELOC_TIC54X_23;
    insn->opcode[0].r_nchars = 4;
    insn->opcode[0].unresolved = 1;
    insn->words = 1;
}

static void setup_standard_relocation(tic54x_insn *insn, int op, int xpc_code)
{
    insn->opcode[op].word = 0;
    insn->opcode[op].r_nchars = 2;
    
    if (amode == c_mode)
    {
        insn->opcode[op].r_type = BFD_RELOC_TIC54X_16_OF_23;
    }
    else if (xpc_code == 2)
    {
        insn->opcode[op].r_type = BFD_RELOC_TIC54X_MS7_OF_23;
    }
    else
    {
        insn->opcode[op].r_type = BFD_RELOC_TIC54X_16_OF_23;
    }
    
    insn->opcode[op].unresolved = 1;
}

static void handle_non_constant_expression(tic54x_insn *insn, struct opstruct *operand, int op, int xpc_code)
{
    setup_standard_relocation(insn, op, xpc_code);
    
    if (amode != c_mode && xpc_code == 1)
    {
        setup_xpc_code_1_relocation(insn, operand);
    }
}

static int encode_dmad(tic54x_insn *insn, struct opstruct *operand, int xpc_code)
{
    int op = 1 + insn->is_lkaddr;
    
    if (!validate_dmad_syntax(operand))
    {
        return 0;
    }
    
    insn->opcode[op].addr_expr = operand->exp;
    
    if (insn->opcode[op].addr_expr.X_op == O_constant)
    {
        handle_constant_expression(insn, op, xpc_code);
    }
    else
    {
        handle_non_constant_expression(insn, operand, op, xpc_code);
    }
    
    return 1;
}

/* 7-bit direct address encoding.  */

static int
encode_address (tic54x_insn *insn, struct opstruct *operand)
{
  insn->opcode[0].addr_expr = operand->exp;

  if (operand->exp.X_op == O_constant)
    {
      insn->opcode[0].word |= (operand->exp.X_add_number & 0x7F);
      return 1;
    }

  if (operand->exp.X_op == O_register)
    {
      as_bad (_("Use the .mmregs directive to use memory-mapped register names such as '%s'"), operand->buf);
    }
  
  insn->opcode[0].r_nchars = 1;
  insn->opcode[0].r_type = BFD_RELOC_TIC54X_PARTLS7;
  insn->opcode[0].unresolved = 1;

  return 1;
}

static int get_lkaddr_mod(struct opstruct *operand)
{
    if (TOUPPER(operand->buf[1]) == 'A')
        return 12;
    if (operand->buf[1] == '(')
        return 15;
    if (strchr(operand->buf, '%') != NULL)
        return 14;
    return 13;
}

static int get_lkaddr_arf(int mod, struct opstruct *operand)
{
    if (mod == 12)
        return operand->buf[3] - '0';
    if (mod == 15)
        return 0;
    return operand->buf[4] - '0';
}

static void set_lkaddr_opcode(tic54x_insn *insn, struct opstruct *operand)
{
    insn->opcode[1].addr_expr = operand->exp;
    
    if (operand->exp.X_op == O_constant)
    {
        insn->opcode[1].word = operand->exp.X_add_number;
    }
    else
    {
        insn->opcode[1].word = 0;
        insn->opcode[1].r_nchars = 2;
        insn->opcode[1].r_type = BFD_RELOC_TIC54X_16_OF_23;
        insn->opcode[1].unresolved = 1;
    }
}

static int handle_lkaddr(tic54x_insn *insn, struct opstruct *operand)
{
    int mod = get_lkaddr_mod(operand);
    int arf = get_lkaddr_arf(mod, operand);
    
    set_lkaddr_opcode(insn, operand);
    
    insn->opcode[0].word |= 0x80 | (mod << 3) | arf;
    return 1;
}

static int get_indirect_arf(struct opstruct *operand)
{
    if (TOUPPER(operand->buf[1]) == 'A')
        return operand->buf[3] - '0';
    return operand->buf[4] - '0';
}

static int get_indirect_mod_simple(struct opstruct *operand, tic54x_insn *insn)
{
    if (operand->buf[1] == '+')
    {
        if (insn->tm->flags & FL_SMR)
            as_warn(_("Address mode *+ARx is write-only. Results of reading are undefined."));
        return 3;
    }
    if (operand->buf[4] == '\0')
        return 0;
    return -1;
}

static int get_indirect_mod_offset(struct opstruct *operand)
{
    #define MOD_DECREMENT_BASE 1
    #define MOD_INCREMENT_BASE 2
    #define MOD_DECREMENT_ZERO 5
    #define MOD_INCREMENT_ZERO 6
    #define MOD_DECREMENT_PERCENT 8
    #define MOD_INCREMENT_PERCENT 10
    
    if (operand->buf[5] == '\0')
        return (operand->buf[4] == '-' ? MOD_DECREMENT_BASE : MOD_INCREMENT_BASE);
    
    if (operand->buf[6] == '\0')
    {
        if (operand->buf[5] == '0')
            return (operand->buf[4] == '-' ? MOD_DECREMENT_ZERO : MOD_INCREMENT_ZERO);
        return (operand->buf[4] == '-' ? MOD_DECREMENT_PERCENT : MOD_INCREMENT_PERCENT);
    }
    
    return -1;
}

static int get_indirect_mod_extended(struct opstruct *operand)
{
    #define MOD_DECREMENT_B 4
    #define MOD_INCREMENT_B 7
    #define MOD_DECREMENT_PERCENT_EXT 9
    #define MOD_INCREMENT_PERCENT_EXT 11
    
    if (TOUPPER(operand->buf[6]) == 'B')
        return (operand->buf[4] == '-' ? MOD_DECREMENT_B : MOD_INCREMENT_B);
    
    if (TOUPPER(operand->buf[6]) == '%')
        return (operand->buf[4] == '-' ? MOD_DECREMENT_PERCENT_EXT : MOD_INCREMENT_PERCENT_EXT);
    
    return -1;
}

static int get_indirect_mod(struct opstruct *operand, tic54x_insn *insn)
{
    int mod = get_indirect_mod_simple(operand, insn);
    if (mod >= 0)
        return mod;
    
    mod = get_indirect_mod_offset(operand);
    if (mod >= 0)
        return mod;
    
    mod = get_indirect_mod_extended(operand);
    if (mod >= 0)
        return mod;
    
    as_bad(_("Unrecognized indirect address format \"%s\""), operand->buf);
    return -1;
}

static int encode_indirect(tic54x_insn *insn, struct opstruct *operand)
{
    if (insn->is_lkaddr)
        return handle_lkaddr(insn, operand);
    
    if (strncasecmp(operand->buf, "*sp (", 4) == 0)
        return encode_address(insn, operand);
    
    int arf = get_indirect_arf(operand);
    int mod = get_indirect_mod(operand, insn);
    
    if (mod < 0)
        return 0;
    
    insn->opcode[0].word |= 0x80 | (mod << 3) | arf;
    return 1;
}

static int is_16bit_hex_fixup_needed(long parse, int min, int max)
{
    return (parse & 0x8000) && min == -32768 && max == 32767;
}

static long apply_16bit_hex_fixup(long parse, int min, int max)
{
    if (is_16bit_hex_fixup_needed(parse, min, max))
        return (short)parse;
    return parse;
}

static int handle_constant_operand(tic54x_insn *insn, struct opstruct *operand, 
                                   int which, int min, int max, unsigned short mask)
{
    long parse = operand->exp.X_add_number;
    long integer = apply_16bit_hex_fixup(parse, min, max);
    
    if (integer >= min && integer <= max)
    {
        insn->opcode[which].word |= (integer & mask);
        return 1;
    }
    
    as_bad(_("Operand '%s' out of range (%d <= x <= %d)"),
           operand->buf, min, max);
    return 0;
}

static bfd_reloc_code_real_type get_reloc_type(unsigned short mask)
{
    #define MASK_PARTMS9 0x1FF
    #define MASK_16OF23  0xFFFF
    #define MASK_PARTLS7 0x7F
    
    if (mask == MASK_PARTMS9)
        return BFD_RELOC_TIC54X_PARTMS9;
    if (mask == MASK_16OF23)
        return BFD_RELOC_TIC54X_16_OF_23;
    if (mask == MASK_PARTLS7)
        return BFD_RELOC_TIC54X_PARTLS7;
    return BFD_RELOC_8;
}

static int get_reloc_size(unsigned short mask)
{
    #define MASK_PARTMS9 0x1FF
    #define MASK_16OF23  0xFFFF
    
    return (mask == MASK_PARTMS9 || mask == MASK_16OF23) ? 2 : 1;
}

static void setup_relocation(tic54x_insn *insn, int which, unsigned short mask)
{
    bfd_reloc_code_real_type rtype = get_reloc_type(mask);
    
    if (rtype == BFD_RELOC_8)
        as_bad(_("Error in relocation handling"));
    
    insn->opcode[which].r_nchars = get_reloc_size(mask);
    insn->opcode[which].r_type = rtype;
    insn->opcode[which].unresolved = 1;
}

static int handle_non_constant_operand(tic54x_insn *insn, int which, unsigned short mask)
{
    if (insn->opcode[which].addr_expr.X_op == O_constant)
    {
        insn->opcode[which].word |= 
            insn->opcode[which].addr_expr.X_add_number & mask;
    }
    else
    {
        setup_relocation(insn, which, mask);
    }
    return 1;
}

static int
encode_integer(tic54x_insn *insn, struct opstruct *operand,
               int which, int min, int max, unsigned short mask)
{
    insn->opcode[which].addr_expr = operand->exp;
    
    if (operand->exp.X_op == O_constant)
        return handle_constant_operand(insn, operand, which, min, max, mask);
    
    return handle_non_constant_operand(insn, which, mask);
}

static int find_condition_code(const char *buf, tic54x_symbol **cc)
{
    *cc = str_hash_find(cc_hash, buf);
    if (!*cc)
    {
        as_bad(_("Unrecognized condition code \"%s\""), buf);
        return 0;
    }
    return 1;
}

static int check_group_mismatch(unsigned int opcode_word, unsigned int cc_value, const char *buf)
{
    if ((opcode_word & CC_GROUP) != (cc_value & CC_GROUP))
    {
        as_bad(_("Condition \"%s\" does not match preceding group"), buf);
        return 0;
    }
    return 1;
}

static int check_accumulator_mismatch(unsigned int opcode_word, unsigned int cc_value, const char *buf)
{
    if ((opcode_word & CC_ACC) != (cc_value & CC_ACC))
    {
        as_bad(_("Condition \"%s\" uses a different accumulator from a preceding condition"), buf);
        return 0;
    }
    return 1;
}

static int check_group1_categories(unsigned int opcode_word, unsigned int cc_value)
{
    if ((opcode_word & CATG_A1) && (cc_value & CATG_A1))
    {
        as_bad(_("Only one comparison conditional allowed"));
        return 0;
    }
    if ((opcode_word & CATG_B1) && (cc_value & CATG_B1))
    {
        as_bad(_("Only one overflow conditional allowed"));
        return 0;
    }
    return 1;
}

static int check_group2_categories(unsigned int opcode_word, unsigned int cc_value, const char *buf)
{
    if (((opcode_word & CATG_A2) && (cc_value & CATG_A2)) ||
        ((opcode_word & CATG_B2) && (cc_value & CATG_B2)) ||
        ((opcode_word & CATG_C2) && (cc_value & CATG_C2)))
    {
        as_bad(_("Duplicate %s conditional"), buf);
        return 0;
    }
    return 1;
}

static int validate_group1_condition(unsigned int opcode_word, unsigned int cc_value, const char *buf)
{
    if (!check_accumulator_mismatch(opcode_word, cc_value, buf))
        return 0;
    
    return check_group1_categories(opcode_word, cc_value);
}

static int validate_condition(unsigned int opcode_word, tic54x_symbol *cc, const char *buf)
{
    if (!check_group_mismatch(opcode_word, cc->value, buf))
        return 0;
    
    if (opcode_word & CC_GROUP)
        return validate_group1_condition(opcode_word, cc->value, buf);
    
    return check_group2_categories(opcode_word, cc->value, buf);
}

#define CC_GROUP 0x40
#define CC_ACC   0x08
#define CATG_A1  0x07
#define CATG_B1  0x30
#define CATG_A2  0x30
#define CATG_B2  0x0C
#define CATG_C2  0x03

static int encode_condition(tic54x_insn *insn, struct opstruct *operand)
{
    tic54x_symbol *cc;
    
    if (!find_condition_code(operand->buf, &cc))
        return 0;
    
    if ((insn->opcode[0].word & 0xFF) != 0)
    {
        if (!validate_condition(insn->opcode[0].word, cc, operand->buf))
            return 0;
    }
    
    insn->opcode[0].word |= cc->value;
    return 1;
}

static int encode_cc3(tic54x_insn *insn, struct opstruct *operand)
{
    const int CC3_MASK = 0x0300;
    int value = get_cc3_value(operand);
    
    if (!is_valid_cc3_value(value, CC3_MASK)) {
        as_bad(_("Unrecognized condition code \"%s\""), operand->buf);
        return 0;
    }
    
    insn->opcode[0].word |= value;
    return 1;
}

static int get_cc3_value(struct opstruct *operand)
{
    tic54x_symbol *cc3 = str_hash_find(cc3_hash, operand->buf);
    return cc3 ? cc3->value : operand->exp.X_add_number << 8;
}

static int is_valid_cc3_value(int value, int mask)
{
    return (value & mask) == value;
}

static int
encode_arx (tic54x_insn *insn, struct opstruct *operand)
{
  #define AR_PREFIX_LENGTH 2
  #define MIN_AR_NUMBER 0
  #define MAX_AR_NUMBER 7
  #define AR_STRING_MIN_LENGTH 3
  #define AR_NUMBER_OFFSET 2

  int arf = strlen (operand->buf) >= AR_STRING_MIN_LENGTH ? operand->buf[AR_NUMBER_OFFSET] - '0' : -1;

  if (strncasecmp ("ar", operand->buf, AR_PREFIX_LENGTH) || arf < MIN_AR_NUMBER || arf > MAX_AR_NUMBER)
    {
      as_bad (_("Invalid auxiliary register (use AR0-AR7)"));
      return 0;
    }
  insn->opcode[0].word |= arf;
  return 1;
}

static int
encode_cc2 (tic54x_insn *insn, struct opstruct *operand)
{
  tic54x_symbol *cc2 = str_hash_find (cc2_hash, operand->buf);

  if (!cc2)
    {
      as_bad (_("Unrecognized condition code \"%s\""), operand->buf);
      return 0;
    }
  insn->opcode[0].word |= cc2->value;
  return 1;
}

static int handle_mmr_operand(tic54x_insn *insn, enum optype *type, struct opstruct *operand)
{
    if (*type != OP_MMR || operand->exp.X_op == O_constant)
        return 1;
    
    if (insn->is_lkaddr)
    {
        as_bad(_("lk addressing modes are invalid for memory-mapped "
                 "register addressing"));
        return 0;
    }
    
    *type = OP_Smem;
    
    if (strncasecmp(operand->buf, "*+ar", 4) == 0)
    {
        as_warn(_("Address mode *+ARx is not allowed in memory-mapped "
                  "register addressing.  Resulting behavior is "
                  "undefined."));
    }
    
    return 1;
}

static int get_word_index(tic54x_insn *insn, int ext)
{
    return ext ? (1 + insn->is_lkaddr) : 0;
}

static int encode_accumulator(tic54x_insn *insn, struct opstruct *operand, int ext, int bit_position)
{
    if (TOUPPER(operand->buf[0]) == 'B')
        insn->opcode[get_word_index(insn, ext)].word |= (1 << bit_position);
    return 1;
}

static int encode_src_operand(tic54x_insn *insn, struct opstruct *operand, int ext)
{
    if (TOUPPER(*operand->buf) == 'B')
    {
        int word_index = get_word_index(insn, ext);
        insn->opcode[word_index].word |= (1 << 9);
        if (insn->using_default_dst)
            insn->opcode[word_index].word |= (1 << 8);
    }
    return 1;
}

static int encode_rnd_operand(tic54x_insn *insn, struct opstruct *operand)
{
    if (!((TOUPPER(operand->buf[0]) == 'B') ^
          ((insn->opcode[0].word & (1 << 8)) != 0)))
    {
        as_bad(_("Destination accumulator for each part of this parallel "
                 "instruction must be different"));
        return 0;
    }
    return 1;
}

static int encode_xy_mem(tic54x_insn *insn, struct opstruct *operand, enum optype type)
{
    int mod = (operand->buf[4] == '\0' ? 0 :
               operand->buf[4] == '-' ? 1 :
               operand->buf[5] == '\0' ? 2 : 3);
    int arf = operand->buf[3] - '0' - 2;
    int code = (mod << 2) | arf;
    insn->opcode[0].word |= (code << (type == OP_Xmem ? 4 : 0));
    return 1;
}

static int encode_mmr_value(tic54x_insn *insn, struct opstruct *operand, enum optype type)
{
    int value = operand->exp.X_add_number;
    
    if (type == OP_MMR)
    {
        insn->opcode[0].word |= value;
        return 1;
    }
    
    if (value < 16 || value > 24)
    {
        as_bad(_("Memory mapped register \"%s\" out of range"), operand->buf);
        return 0;
    }
    
    if (type == OP_MMRX)
        insn->opcode[0].word |= (value - 16) << 4;
    else
        insn->opcode[0].word |= (value - 16);
    
    return 1;
}

static int encode_123_operand(tic54x_insn *insn, struct opstruct *operand)
{
    int value = operand->exp.X_add_number;
    int code;
    
    if (value < 1 || value > 3)
    {
        as_bad(_("Invalid operand (use 1, 2, or 3)"));
        return 0;
    }
    
    code = value == 1 ? 0 : value == 2 ? 0x2 : 0x1;
    insn->opcode[0].word |= (code << 8);
    return 1;
}

static int encode_sbit_operand(tic54x_insn *insn, struct opstruct *operand)
{
    tic54x_symbol *sbit = str_hash_find(sbit_hash, operand->buf);
    int value = is_absolute(operand) ?
                operand->exp.X_add_number : (sbit ? sbit->value : -1);
    int reg = 0;
    
    if (insn->opcount == 1)
    {
        if (!sbit)
        {
            as_bad(_("A status register or status bit name is required"));
            return 0;
        }
        if (sbit > (tic54x_symbol *)str_hash_find(sbit_hash, "ovb"))
            reg = 1;
    }
    
    if (value == -1)
    {
        as_bad(_("Unrecognized status bit \"%s\""), operand->buf);
        return 0;
    }
    
    insn->opcode[0].word |= value;
    insn->opcode[0].word |= (reg << 9);
    return 1;
}

static int encode_n_operand(tic54x_insn *insn, struct opstruct *operand)
{
    if (strcasecmp(operand->buf, "st0") == 0 ||
        strcasecmp(operand->buf, "st1") == 0)
    {
        insn->opcode[0].word |= ((uint16_t)(operand->buf[2] - '0')) << 9;
        return 1;
    }
    
    if (operand->exp.X_op == O_constant &&
        (operand->exp.X_add_number == 0 ||
         operand->exp.X_add_number == 1))
    {
        insn->opcode[0].word |= ((uint16_t)(operand->exp.X_add_number)) << 9;
        return 1;
    }
    
    as_bad(_("Invalid status register \"%s\""), operand->buf);
    return 0;
}

static int encode_12_operand(tic54x_insn *insn, struct opstruct *operand)
{
    if (operand->exp.X_add_number != 1 &&
        operand->exp.X_add_number != 2)
    {
        as_bad(_("Operand \"%s\" out of range (use 1 or 2)"), operand->buf);
        return 0;
    }
    insn->opcode[0].word |= (operand->exp.X_add_number - 1) << 9;
    return 1;
}

static int encode_operand(tic54x_insn *insn, enum optype type, struct opstruct *operand)
{
    int ext = (insn->tm->flags & FL_EXT) != 0;
    
    if (!handle_mmr_operand(insn, &type, operand))
        return 0;
    
    switch (type)
    {
    case OP_None:
        return 1;
    case OP_dmad:
        return encode_dmad(insn, operand, 0);
    case OP_SRC:
        return encode_src_operand(insn, operand, ext);
    case OP_RND:
        return encode_rnd_operand(insn, operand);
    case OP_SRC1:
    case OP_DST:
        return encode_accumulator(insn, operand, ext, 8);
    case OP_Xmem:
    case OP_Ymem:
        return encode_xy_mem(insn, operand, type);
    case OP_Lmem:
    case OP_Smem:
        if (!is_indirect(operand))
            return encode_address(insn, operand);
    case OP_Sind:
        return encode_indirect(insn, operand);
    case OP_xpmad_ms7:
        return encode_dmad(insn, operand, 2);
    case OP_xpmad:
        return encode_dmad(insn, operand, 1);
    case OP_PA:
    case OP_pmad:
        return encode_dmad(insn, operand, 0);
    case OP_ARX:
        return encode_arx(insn, operand);
    case OP_MMRX:
    case OP_MMRY:
    case OP_MMR:
        return encode_mmr_value(insn, operand, type);
    case OP_B:
    case OP_A:
        return 1;
    case OP_SHFT:
        return encode_integer(insn, operand, ext + insn->is_lkaddr, 0, 15, 0xF);
    case OP_SHIFT:
        return encode_integer(insn, operand, ext + insn->is_lkaddr, -16, 15, 0x1F);
    case OP_lk:
        return encode_integer(insn, operand, 1 + insn->is_lkaddr, -32768, 32767, 0xFFFF);
    case OP_CC:
        return encode_condition(insn, operand);
    case OP_CC2:
        return encode_cc2(insn, operand);
    case OP_CC3:
        return encode_cc3(insn, operand);
    case OP_BITC:
        return encode_integer(insn, operand, 0, 0, 15, 0xF);
    case OP_k8:
        return encode_integer(insn, operand, 0, -128, 127, 0xFF);
    case OP_123:
        return encode_123_operand(insn, operand);
    case OP_031:
        return encode_integer(insn, operand, 0, 0, 31, 0x1F);
    case OP_k8u:
        return encode_integer(insn, operand, 0, 0, 255, 0xFF);
    case OP_lku:
        return encode_integer(insn, operand, 1 + insn->is_lkaddr, 0, 65535, 0xFFFF);
    case OP_SBIT:
        return encode_sbit_operand(insn, operand);
    case OP_N:
        return encode_n_operand(insn, operand);
    case OP_k5:
        return encode_integer(insn, operand, 0, -16, 15, 0x1F);
    case OP_k3:
        return encode_integer(insn, operand, 0, 0, 7, 0x7);
    case OP_k9:
        return encode_integer(insn, operand, 0, 0, 0x1FF, 0x1FF);
    case OP_12:
        return encode_12_operand(insn, operand);
    case OP_16:
    case OP_T:
    case OP_TS:
    case OP_ASM:
    case OP_TRN:
    case OP_DP:
    case OP_ARP:
        return 1;
    default:
        return 0;
    }
    
    return 1;
}

static void set_section_code_flags(void)
{
    flagword oldflags = bfd_section_flags(now_seg);
    flagword flags = oldflags | SEC_CODE;

    if (!bfd_set_section_flags(now_seg, flags))
        as_warn(_("error setting flags for \"%s\": %s"),
                bfd_section_name(now_seg),
                bfd_errmsg(bfd_get_error()));
}

static int get_opcode_size(tic54x_opcode *opcode)
{
    if (opcode->unresolved && opcode->r_type == BFD_RELOC_TIC54X_23)
        return 4;
    return 2;
}

static void write_opcode_bytes(char *p, tic54x_opcode *opcode, int size)
{
    if (size == 2)
        md_number_to_chars(p, opcode->word, 2);
    else
        md_number_to_chars(p, (valueT)opcode->word << 16, 4);
}

static void handle_unresolved_opcode(char *p, tic54x_opcode *opcode)
{
    if (opcode->unresolved)
        fix_new_exp(frag_now, p - frag_now->fr_literal,
                   opcode->r_nchars, &opcode->addr_expr,
                   false, opcode->r_type);
}

static void emit_single_opcode(tic54x_opcode *opcode)
{
    int size = get_opcode_size(opcode);
    char *p = frag_more(size);
    
    write_opcode_bytes(p, opcode, size);
    handle_unresolved_opcode(p, opcode);
}

static void emit_insn(tic54x_insn *insn)
{
    int i;
    
    set_section_code_flags();
    
    for (i = 0; i < insn->words; i++)
    {
        emit_single_opcode(&insn->opcode[i]);
    }
}

/* Convert the operand strings into appropriate opcode values
   return the total number of words used by the instruction.  */

static int is_lk_addressing(const operand *op)
{
    int op_type = OPTYPE(op->type);
    return (op_type == OP_Smem || op_type == OP_Lmem || op_type == OP_Sind) &&
           strchr(op->buf, '(') != NULL &&
           strncasecmp(op->buf, "*sp (", 4) != 0;
}

static void detect_lk_addressing(tic54x_insn *insn)
{
    if (insn->tm->flags & FL_PAR)
        return;
    
    for (int i = 0; i < insn->opcount; i++)
    {
        if (is_lk_addressing(&insn->operands[i]))
        {
            insn->is_lkaddr = 1;
            insn->lkoperand = i;
            break;
        }
    }
}

static void setup_opcode_words(tic54x_insn *insn)
{
    insn->words = insn->tm->words + insn->is_lkaddr;
    insn->opcode[0].word = insn->tm->opcode;
    
    if (insn->tm->flags & FL_EXT)
        insn->opcode[1 + insn->is_lkaddr].word = insn->tm->opcode2;
}

static int encode_all_operands(tic54x_insn *insn)
{
    for (int i = 0; i < insn->opcount; i++)
    {
        if (!encode_operand(insn, insn->operands[i].type, &insn->operands[i]))
            return 0;
    }
    
    if (insn->tm->flags & FL_PAR)
    {
        for (int i = 0; i < insn->paropcount; i++)
        {
            if (!encode_operand(insn, insn->paroperands[i].type, &insn->paroperands[i]))
                return 0;
        }
    }
    
    return 1;
}

static int build_insn(tic54x_insn *insn)
{
    detect_lk_addressing(insn);
    setup_opcode_words(insn);
    
    if (!encode_all_operands(insn))
        return 0;
    
    emit_insn(insn);
    return insn->words;
}

#define is_zero(op) ((op).exp.X_op == O_constant && (op).exp.X_add_number == 0)

static int handle_duplicate_accumulator(tic54x_insn *insn)
{
    if (insn->opcount > 1
        && is_accumulator(&insn->operands[insn->opcount - 2])
        && is_accumulator(&insn->operands[insn->opcount - 1])
        && strcasecmp(insn->operands[insn->opcount - 2].buf,
                      insn->operands[insn->opcount - 1].buf) == 0)
    {
        --insn->opcount;
        insn->using_default_dst = 1;
        return 1;
    }
    return 0;
}

static int collapse_zero_shift(tic54x_insn *insn)
{
    insn->operands[1] = insn->operands[2];
    insn->opcount = 2;
    return 1;
}

static int optimize_add(tic54x_insn *insn)
{
    if (handle_duplicate_accumulator(insn))
        return 1;

    if ((OPTYPE(insn->tm->operand_types[0]) == OP_Xmem
         && OPTYPE(insn->tm->operand_types[1]) == OP_SHFT
         && is_zero(insn->operands[1]))
        || (OPTYPE(insn->tm->operand_types[0]) == OP_Smem
            && OPTYPE(insn->tm->operand_types[1]) == OP_SHIFT
            && is_type(&insn->operands[1], OP_SHIFT)
            && is_zero(insn->operands[1]) && insn->opcount == 3))
    {
        return collapse_zero_shift(insn);
    }
    return 0;
}

static int optimize_ld(tic54x_insn *insn)
{
    if (insn->opcount != 3 || insn->operands[0].type == OP_SRC)
        return 0;

    if ((OPTYPE(insn->tm->operand_types[1]) == OP_SHIFT
         || OPTYPE(insn->tm->operand_types[1]) == OP_SHFT)
        && is_zero(insn->operands[1])
        && (OPTYPE(insn->tm->operand_types[0]) != OP_lk
            || (insn->operands[0].exp.X_op == O_constant
                && insn->operands[0].exp.X_add_number <= 255
                && insn->operands[0].exp.X_add_number >= 0)))
    {
        return collapse_zero_shift(insn);
    }
    return 0;
}

static int optimize_store(tic54x_insn *insn)
{
    if ((OPTYPE(insn->tm->operand_types[1]) == OP_SHIFT
         || OPTYPE(insn->tm->operand_types[1]) == OP_SHFT)
        && is_zero(insn->operands[1]))
    {
        return collapse_zero_shift(insn);
    }
    return 0;
}

static int optimize_sub(tic54x_insn *insn)
{
    if (handle_duplicate_accumulator(insn))
        return 1;

    if (((OPTYPE(insn->tm->operand_types[0]) == OP_Smem
          && OPTYPE(insn->tm->operand_types[1]) == OP_SHIFT)
         || (OPTYPE(insn->tm->operand_types[0]) == OP_Xmem
             && OPTYPE(insn->tm->operand_types[1]) == OP_SHFT))
        && is_zero(insn->operands[1])
        && insn->opcount == 3)
    {
        return collapse_zero_shift(insn);
    }
    return 0;
}

static int
optimize_insn(tic54x_insn *insn)
{
    if (strcasecmp(insn->tm->name, "add") == 0)
        return optimize_add(insn);
    
    if (strcasecmp(insn->tm->name, "ld") == 0)
        return optimize_ld(insn);
    
    if (strcasecmp(insn->tm->name, "sth") == 0
        || strcasecmp(insn->tm->name, "stl") == 0)
        return optimize_store(insn);
    
    if (strcasecmp(insn->tm->name, "sub") == 0)
        return optimize_sub(insn);
    
    return 0;
}

/* Find a matching template if possible, and get the operand strings.  */

static int find_instruction(tic54x_insn *insn)
{
    insn->tm = str_hash_find(op_hash, insn->mnemonic);
    if (!insn->tm)
    {
        as_bad(_("Unrecognized instruction \"%s\""), insn->mnemonic);
        return 0;
    }
    return 1;
}

static int parse_operands(tic54x_insn *insn, char *line)
{
    insn->opcount = get_operands(insn->operands, line);
    return insn->opcount >= 0;
}

static int is_valid_operand_count(tic54x_insn *insn)
{
    return insn->opcount >= insn->tm->minops && 
           insn->opcount <= insn->tm->maxops;
}

static int try_match_variation(tic54x_insn *insn)
{
    if (!is_valid_operand_count(insn))
        return 0;
    
    return operands_match(insn, &insn->operands[0], insn->opcount,
                         insn->tm->operand_types,
                         insn->tm->minops, insn->tm->maxops);
}

static int apply_optimization(tic54x_insn *insn)
{
    if (optimize_insn(insn))
    {
        insn->tm = str_hash_find(op_hash, insn->mnemonic);
        return 1;
    }
    return 0;
}

static int find_matching_variation(tic54x_insn *insn, char *line)
{
    while (insn->tm->name && strcasecmp(insn->tm->name, insn->mnemonic) == 0)
    {
        if (try_match_variation(insn))
        {
            if (apply_optimization(insn))
                continue;
            return 1;
        }
        ++(insn->tm);
    }
    
    as_bad(_("Unrecognized operand list '%s' for instruction '%s'"),
           line, insn->mnemonic);
    return 0;
}

static int tic54x_parse_insn(tic54x_insn *insn, char *line)
{
    if (!find_instruction(insn))
        return 0;
    
    if (!parse_operands(insn, line))
        return 0;
    
    return find_matching_variation(insn, line);
}

/* We set this in start_line_hook, 'cause if we do a line replacement, we
   won't be able to see the next line.  */
static int parallel_on_next_line_hint = 0;

/* See if this is part of a parallel instruction
   Look for a subsequent line starting with "||".  */

static int
next_line_shows_parallel (char *next_line)
{
  while (*next_line != 0
	 && (is_whitespace (*next_line) || is_end_of_stmt (*next_line)))
    ++next_line;

  return (next_line[0] == PARALLEL_SEPARATOR
	  && next_line[1] == PARALLEL_SEPARATOR);
}

static int
validate_parallel_instruction(tic54x_insn *insn)
{
    insn->tm = str_hash_find(parop_hash, insn->mnemonic);
    if (!insn->tm)
    {
        as_bad(_("Unrecognized parallel instruction \"%s\""),
               insn->mnemonic);
        return 0;
    }
    return 1;
}

static int
check_parallel_operands(tic54x_insn *insn)
{
    const int REQUIRED_OPERAND_COUNT = 2;
    
    if (insn->opcount == REQUIRED_OPERAND_COUNT &&
        operands_match(insn, &insn->operands[0], insn->opcount,
                      insn->tm->operand_types, REQUIRED_OPERAND_COUNT, 
                      REQUIRED_OPERAND_COUNT))
    {
        return 1;
    }
    return 0;
}

static int
try_match_parallel_instruction(tic54x_insn *insn, char *line)
{
    while (insn->tm->name && 
           strcasecmp(insn->tm->name, insn->mnemonic) == 0)
    {
        insn->opcount = get_operands(insn->operands, line);
        if (insn->opcount < 0)
            return 0;
            
        if (check_parallel_operands(insn))
            return 1;
            
        ++(insn->tm);
    }
    return 0;
}

static int
tic54x_parse_parallel_insn_firstline(tic54x_insn *insn, char *line)
{
    if (!validate_parallel_instruction(insn))
        return 0;
        
    return try_match_parallel_instruction(insn, line);
}

/* Parse the second line of a two-line parallel instruction.  */

static int is_valid_parallel_mnemonic(const tic54x_insn *insn)
{
    return strcasecmp(insn->tm->parname, insn->parmnemonic) == 0;
}

static int has_valid_operand_count(const tic54x_insn *insn)
{
    return insn->paropcount >= insn->tm->minops && 
           insn->paropcount <= insn->tm->maxops;
}

static int has_matching_operands(const tic54x_insn *insn)
{
    return operands_match(insn, insn->paroperands,
                         insn->paropcount,
                         insn->tm->paroperand_types,
                         insn->tm->minops, insn->tm->maxops);
}

static int find_matching_parallel_instruction(tic54x_insn *insn)
{
    int valid_mnemonic = 0;
    
    while (insn->tm->name && strcasecmp(insn->tm->name, insn->mnemonic) == 0)
    {
        if (is_valid_parallel_mnemonic(insn))
        {
            valid_mnemonic = 1;
            
            if (has_valid_operand_count(insn) && has_matching_operands(insn))
                return 1;
        }
        ++(insn->tm);
    }
    
    return valid_mnemonic;
}

static void report_parallel_instruction_error(const tic54x_insn *insn, int valid_mnemonic)
{
    if (valid_mnemonic)
        as_bad(_("Invalid operand (s) for parallel instruction \"%s\""),
               insn->parmnemonic);
    else
        as_bad(_("Unrecognized parallel instruction combination \"%s || %s\""),
               insn->mnemonic, insn->parmnemonic);
}

static int tic54x_parse_parallel_insn_lastline(tic54x_insn *insn, char *line)
{
    insn->paropcount = get_operands(insn->paroperands, line);
    
    int valid_mnemonic = find_matching_parallel_instruction(insn);
    
    if (valid_mnemonic == 1)
        return 1;
    
    report_parallel_instruction_error(insn, valid_mnemonic);
    return 0;
}

/* If quotes found, return copy of line up to closing quote;
   otherwise up until terminator.
   If it's a string, pass as-is; otherwise attempt substitution symbol
   replacement on the value.  */

static char *extract_digit_string(char *line, char **str)
{
    char *ptr = line;
    while (ISDIGIT(*ptr))
        ++ptr;
    *str = xmemdup0(line, ptr - line);
    return ptr;
}

static char *extract_quoted_string(char *line, char **str, int nosub)
{
    char *savedp = input_line_pointer;
    int len;
    
    input_line_pointer = line;
    *str = demand_copy_C_string(&len);
    char *endp = input_line_pointer;
    input_line_pointer = savedp;
    
    if (!nosub && **str == ':')
        *str = subsym_substitute(*str, 1);
    
    return endp;
}

static char *find_terminator(char *ptr, const char *terminators)
{
    while (*ptr)
    {
        const char *term = terminators;
        while (*term)
        {
            if (*ptr == *term)
                return ptr;
            ++term;
        }
        ++ptr;
    }
    return ptr;
}

static void perform_simple_substitution(char **str)
{
    subsym_ent_t *ent = subsym_lookup(*str, macro_level);
    if (ent && !ent->isproc)
        *str = ent->u.s;
}

static char *extract_unquoted_string(char *line, const char *terminators, char **str, int nosub)
{
    char *endp = find_terminator(line, terminators);
    *str = xmemdup0(line, endp - line);
    
    if (!nosub)
        perform_simple_substitution(str);
    
    return endp;
}

static char *subsym_get_arg(char *line, const char *terminators, char **str, int nosub)
{
    if (ISDIGIT(*line))
        return extract_digit_string(line, str);
    
    if (*line == '"')
        return extract_quoted_string(line, str, nosub);
    
    return extract_unquoted_string(line, terminators, str, nosub);
}

/* Replace the given substitution string.
   We start at the innermost macro level, so that existing locals remain local
   Note: we're treating macro args identically to .var's; I don't know if
   that's compatible w/TI's assembler.  */

static void init_subsym_entry(subsym_ent_t *ent, char *value)
{
    ent->u.s = value;
    ent->freekey = 0;
    ent->freeval = 0;
    ent->isproc = 0;
    ent->ismath = 0;
}

static int find_existing_hash_level(char *name)
{
    int i;
    for (i = macro_level; i > 0; i--)
    {
        if (str_hash_find(subsym_hash[i], name))
        {
            return i;
        }
    }
    return 0;
}

static void subsym_create_or_replace(char *name, char *value)
{
    subsym_ent_t *ent = xmalloc(sizeof(*ent));
    init_subsym_entry(ent, value);
    
    int hash_level = find_existing_hash_level(name);
    str_hash_insert(subsym_hash[hash_level], name, ent, 1);
}

/* Look up the substitution string replacement for the given symbol.
   Start with the innermost macro substitution table given and work
   outwards.  */

static subsym_ent_t *
subsym_lookup (char *name, int nest_level)
{
  void *value = str_hash_find (subsym_hash[nest_level], name);

  if (value || nest_level == 0)
    return value;

  return subsym_lookup (name, nest_level - 1);
}

/* Do substitution-symbol replacement on the given line (recursively).
   return the argument if no substitution was done

   Also look for built-in functions ($func (arg)) and local labels.

   If FORCED is set, look for forced substitutions of the form ':SYMBOL:'.  */

static int is_conditional_line(const char *line)
{
  return strstr(line, ".if") || strstr(line, ".elseif") || strstr(line, ".break");
}

static int is_eval_line(const char *line)
{
  return strstr(line, ".eval") || strstr(line, ".asg");
}

static int is_macro_definition(const char *line)
{
  return strstr(line, ".macro") != NULL;
}

static char *handle_triple_quotes(char *ptr, int *changed)
{
  if (ptr[0] == '"' && ptr[1] == '"' && ptr[2] == '"')
    {
      ptr[1] = '\\';
      char *tmp = strstr(ptr + 2, "\"\"\"");
      if (tmp)
        tmp[0] = '\\';
      *changed = 1;
    }
  return ptr;
}

static char *handle_single_equals(char *ptr, char **head, char **replacement, int line_conditional, int *changed)
{
  if (!line_conditional || *ptr != '=')
    return ptr;
    
  if (ptr[1] == '=')
    return ptr + 2;
    
  *ptr++ = '\0';
  char *tmp = concat(*head, "==", ptr, (char *) NULL);
  ptr = tmp + strlen(*head) + 2;
  free(*replacement);
  *head = *replacement = tmp;
  *changed = 1;
  return ptr;
}

static char *create_local_label_value(const char *name, int macro_level)
{
  char *value = str_hash_find(local_label_hash[macro_level], name);
  if (value != NULL)
    return value;
    
  char digit[11];
  char *namecopy = xstrdup(name);
  value = strcpy(xmalloc(strlen(name) + sizeof(digit) + 1), name);
  
  if (*value != '$')
    value[strlen(value) - 1] = '\0';
    
  sprintf(digit, ".%d", local_label_id++);
  strcat(value, digit);
  str_hash_insert(local_label_hash[macro_level], namecopy, value, 0);
  
  return value;
}

static int is_local_label(const char *name)
{
  return (*name == '$' && ISDIGIT(name[1]) && name[2] == '\0') ||
         name[strlen(name) - 1] == '?';
}

static char *process_math_function(const subsym_proc_entry *entry, char *ptr, char **tail, int *recurse)
{
  float farg1 = (float) strtod(ptr, &ptr);
  float farg2 = 0;
  
  if (entry->nargs == 2)
    {
      if (*ptr++ != ',')
        {
          as_bad(_("Expecting second argument"));
          return NULL;
        }
      farg2 = (float) strtod(ptr, &ptr);
    }
    
  char *value = XNEWVEC(char, 128);
  
  if (entry->type == 2)
    {
      int result = (*entry->proc.i)(farg1, farg2);
      sprintf(value, "%d", result);
    }
  else
    {
      float result = (*entry->proc.f)(farg1, farg2);
      sprintf(value, "%f", result);
    }
    
  if (*ptr++ != ')')
    {
      as_bad(_("Extra junk in function call, expecting ')'"));
      return NULL;
    }
    
  *tail = ptr;
  *recurse = 0;
  return value;
}

static char *process_string_function(const subsym_proc_entry *entry, char *ptr, char **tail)
{
  char *arg1 = NULL;
  char *arg2 = NULL;
  int arg_type[2] = { *ptr == '"', 0 };
  int ismember = !strcmp(entry->name, "$ismember");
  
  ptr = subsym_get_arg(ptr, ",)", &arg1, ismember);
  if (!arg1)
    return NULL;
    
  if (entry->nargs == 2)
    {
      if (*ptr++ != ',')
        {
          as_bad(_("Function expects two arguments"));
          return NULL;
        }
      arg_type[1] = (ISDIGIT(*ptr)) ? 2 : (*ptr == '"');
      ptr = subsym_get_arg(ptr, ")", &arg2, ismember);
    }
    
  if ((!strcmp(entry->name, "$firstch") || !strcmp(entry->name, "$lastch")) && arg_type[1] != 2)
    {
      as_bad(_("Expecting character constant argument"));
      return NULL;
    }
    
  if (ismember && (arg_type[0] != 0 || arg_type[1] != 0))
    {
      as_bad(_("Both arguments must be substitution symbols"));
      return NULL;
    }
    
  if (*ptr++ != ')')
    {
      as_bad(_("Extra junk in function call, expecting ')'"));
      return NULL;
    }
    
  int val = (*entry->proc.s)(arg1, arg2);
  char *value = XNEWVEC(char, 64);
  sprintf(value, "%d", val);
  *tail = ptr;
  return value;
}

static char *process_builtin_function(subsym_ent_t *ent, char *name, char *ptr, int c, char **tail, int *recurse)
{
  const subsym_proc_entry *entry = ent->u.p;
  
  *ptr = c;
  if (!ent->isproc)
    {
      as_bad(_("Unrecognized substitution symbol function"));
      return NULL;
    }
    
  if (*ptr != '(')
    {
      as_bad(_("Missing '(' after substitution symbol function"));
      return NULL;
    }
    
  ++ptr;
  
  if (ent->ismath)
    return process_math_function(entry, ptr, tail, recurse);
  else
    return process_string_function(entry, ptr, tail);
}

static char *process_forced_subscript(char *value, char *tail, int c)
{
  if (c != '(')
    return value;
    
  unsigned beg, len = 1;
  char *newval = xstrdup(value);
  char *savedp = input_line_pointer;
  
  input_line_pointer = tail + 1;
  beg = get_absolute_expression();
  
  if (beg < 1)
    {
      as_bad(_("Invalid subscript (use 1 to %d)"), (int)strlen(value));
      input_line_pointer = savedp;
      return NULL;
    }
    
  if (*input_line_pointer == ',')
    {
      ++input_line_pointer;
      len = get_absolute_expression();
      if (beg + len > strlen(value))
        {
          as_bad(_("Invalid length (use 0 to %d)"), (int)strlen(value) - beg);
          input_line_pointer = savedp;
          return NULL;
        }
    }
    
  newval += beg - 1;
  newval[len] = 0;
  
  if (*input_line_pointer++ != ')')
    {
      as_bad(_("Missing ')' in subscripted substitution symbol expression"));
      input_line_pointer = savedp;
      return NULL;
    }
    
  input_line_pointer = savedp;
  return newval;
}

static char *apply_replacement(char *head, char *name, char *value, char *tail, int c, int forced, char **ptr_out)
{
  if (forced)
    {
      value = process_forced_subscript(value, tail, c);
      if (!value)
        return NULL;
        
      name[-1] = 0;
      
      if (c == '(' && *input_line_pointer == ')')
        {
          ++input_line_pointer;
          tail = input_line_pointer;
          c = *tail;
        }
        
      if (c != ':')
        {
          as_bad(_("Missing forced substitution terminator ':'"));
          return NULL;
        }
      ++tail;
    }
  else
    *tail = c;
    
  char *tmp = xmalloc(strlen(head) + strlen(value) + strlen(tail) + 2);
  strcpy(tmp, head);
  strcat(tmp, value);
  strcat(tmp, tail);
  
  *ptr_out = tmp + strlen(head) + strlen(value);
  return tmp;
}

static char *process_symbol(char *ptr, char *head, char **replacement, int forced, int eval_symbol, int macro_level, int *changed)
{
  char *name;
  char *savedp = input_line_pointer;
  int c;
  subsym_ent_t *ent = NULL;
  char *value = NULL;
  char *tail;
  int recurse = 1;
  
  if (forced)
    ++ptr;
    
  input_line_pointer = ptr;
  c = get_symbol_name(&name);
  
  if (c == '?')
    {
      *input_line_pointer++ = c;
      c = *input_line_pointer;
      *input_line_pointer = '\0';
    }
    
  if (str_hash_find(subsym_recurse_hash, name) == NULL)
    {
      ent = subsym_lookup(name, macro_level);
      if (ent && !ent->isproc)
        value = ent->u.s;
    }
  else
    as_warn(_("%s symbol recursion stopped at second appearance of '%s'"),
            forced ? "Forced substitution" : "Substitution", name);
            
  ptr = tail = input_line_pointer;
  input_line_pointer = savedp;
  
  if (is_local_label(name))
    {
      value = create_local_label_value(name, macro_level);
      ptr = tail;
    }
  else if (ent != NULL && *name == '$')
    {
      value = process_builtin_function(ent, name, ptr, c, &tail, &recurse);
      if (!value)
        {
          *ptr = c;
          return ptr;
        }
      c = *tail;
    }
    
  if (value != NULL && !eval_symbol)
    {
      if (recurse)
        {
          str_hash_insert(subsym_recurse_hash, name, name, 0);
          value = subsym_substitute(value, macro_level > 0);
          str_hash_delete(subsym_recurse_hash, name);
        }
        
      *name = 0;
      char *new_ptr;
      char *tmp = apply_replacement(head, name, value, tail, c, forced, &new_ptr);
      
      if (!tmp)
        {
          *ptr = c;
          return ptr;
        }
        
      free(*replacement);
      *replacement = tmp;
      *changed = 1;
      return new_ptr;
    }
    
  *ptr = c;
  return ptr;
}

static char *
subsym_substitute (char *line, int forced)
{
  char *replacement;
  char *head;
  char *ptr;
  int changed = 0;
  int eval_line = 0;
  int eval_symbol = 0;
  char *eval_end = NULL;
  int line_conditional = 0;
  char current_char;
  
  line_conditional = is_conditional_line(line);
  eval_line = is_eval_line(line);
  
  if (is_macro_definition(line))
    return line;
    
  replacement = xstrdup(line);
  ptr = head = replacement;
  
  while (!is_end_of_stmt(current_char = *ptr))
    {
      if (eval_line)
        eval_end = strrchr(ptr, ',');
        
      ptr = handle_triple_quotes(ptr, &changed);
      
      if (line_conditional && current_char == '=')
        {
          ptr = handle_single_equals(ptr, &head, &replacement, line_conditional, &changed);
          continue;
        }
        
      if (eval_line && ptr >= eval_end)
        eval_symbol = 1;
        
      if ((forced && current_char == ':') || (!forced && is_name_beginner(current_char)))
        {
          ptr = process_symbol(ptr, head, &replacement, forced, eval_symbol, macro_level, &changed);
          head = replacement;
        }
      else
        {
          ++ptr;
        }
    }
    
  if (changed)
    return replacement;
    
  free(replacement);
  return line;
}

/* We use this to handle substitution symbols
   hijack input_line_pointer, replacing it with our substituted string.

   .sslist should enable listing the line after replacements are made...

   returns the new buffer limit.  */

void
tic54x_start_line_hook (void)
{
  char *line, *endp;
  char *replacement = NULL;

  endp = find_end_of_statement(input_line_pointer);
  line = xmemdup0 (input_line_pointer, endp - input_line_pointer);

  parallel_on_next_line_hint = next_line_shows_parallel (endp);

  replacement = perform_substitutions(line);

  if (replacement != line)
    {
      process_replacement(replacement, endp);
      free (replacement);
      free (line);
      substitution_line = 1;
    }
  else
    {
      free (line);
      substitution_line = 0;
    }
}

static char *find_end_of_statement(char *start)
{
  char *endp = start;
  while (*endp != 0 && !is_end_of_stmt(*endp))
    endp++;
  if (*endp != 0)
    endp++;
  return endp;
}

static char *perform_substitutions(char *line)
{
  char *replacement;
  
  if (macro_level > 0)
    replacement = subsym_substitute (line, 1);
  else
    replacement = line;
  
  return subsym_substitute (replacement, 0);
}

static void process_replacement(char *replacement, char *endp)
{
  char *tmp = replacement;
  char *comment = strchr (replacement, ';');
  char endc = replacement[strlen (replacement) - 1];

  clean_up_comment(comment, endc, replacement);
  tmp = compact_leading_whitespace(tmp);
  
  input_line_pointer = endp;
  input_scrub_insert_line (tmp);
}

static void clean_up_comment(char *comment, char endc, char *replacement)
{
  if (comment != NULL)
    {
      comment[0] = endc;
      comment[1] = 0;
      --comment;
    }
  else
    comment = replacement + strlen (replacement) - 1;

  trim_trailing_whitespace(comment, endc);
}

static void trim_trailing_whitespace(char *comment, char endc)
{
  while (is_whitespace (*comment))
    {
      comment[0] = endc;
      comment[1] = 0;
      --comment;
    }
}

static char *compact_leading_whitespace(char *tmp)
{
  while (is_whitespace (tmp[0]) && is_whitespace (tmp[1]))
    ++tmp;
  return tmp;
}

/* This is the guts of the machine-dependent assembler.  STR points to a
   machine dependent instruction.  This function is supposed to emit
   the frags/bytes it assembles to.  */
void
md_assemble (char *line)
{
  static int repeat_slot = 0;
  static int delay_slots = 0;
  static int is_parallel = 0;
  static tic54x_insn insn;
  char *lptr;
  char *savedp = input_line_pointer;
  int c;

  input_line_pointer = line;
  c = get_symbol_name (&line);

  initialize_cpu_and_address_mode();
  
  if (is_parallel)
    {
      process_parallel_insn_continuation(&insn, line, c, savedp, &is_parallel, &delay_slots);
      return;
    }

  memset (&insn, 0, sizeof (insn));
  strcpy (insn.mnemonic, line);
  lptr = input_line_pointer;
  *lptr = c;
  input_line_pointer = savedp;

  if (check_and_process_parallel_insn(&insn, line, lptr, &is_parallel))
    return;

  if (tic54x_parse_insn (&insn, lptr))
    {
      process_parsed_instruction(&insn, &delay_slots, &repeat_slot);
    }
}

static void initialize_cpu_and_address_mode(void)
{
  if (cpu == VNONE)
    cpu = V542;
  if (address_mode_needs_set)
    {
      set_address_mode (amode);
      address_mode_needs_set = 0;
    }
  if (cpu_needs_set)
    {
      set_cpu (cpu);
      cpu_needs_set = 0;
    }
  assembly_begun = 1;
}

static void process_parallel_insn_continuation(tic54x_insn *insn, char *line, int c, 
                                                char *savedp, int *is_parallel, int *delay_slots)
{
  char *lptr;
  
  *is_parallel = 0;
  strcpy (insn->parmnemonic, line);
  lptr = input_line_pointer;
  *lptr = c;
  input_line_pointer = savedp;

  if (tic54x_parse_parallel_insn_lastline (insn, lptr))
    {
      int words = build_insn (insn);
      validate_delay_slot_fit(words, delay_slots);
    }
}

static int check_and_process_parallel_insn(tic54x_insn *insn, char *line, char *lptr, int *is_parallel)
{
  char *parallel_marker = strstr (line, "||");
  
  if (parallel_marker == NULL && !parallel_on_next_line_hint)
    return 0;

  if (parallel_marker != NULL)
    *parallel_marker = '\0';

  if (tic54x_parse_parallel_insn_firstline (insn, lptr))
    {
      *is_parallel = 1;
      if (parallel_marker != NULL)
        {
          while (is_whitespace (parallel_marker[2]))
            ++parallel_marker;
          md_assemble (parallel_marker + 2);
        }
    }
  else
    {
      as_bad (_("Unrecognized parallel instruction '%s'"), line);
    }
  return 1;
}

static void process_parsed_instruction(tic54x_insn *insn, int *delay_slots, int *repeat_slot)
{
  int words;
  
  if (!validate_instruction_cpu_requirements(insn))
    return;
  if (!validate_instruction_addressing_mode(insn))
    return;

  words = build_insn (insn);

  handle_delay_slot_instruction(insn, words, delay_slots);
  handle_repeat_slot_instruction(insn, repeat_slot);
  update_instruction_state_flags(insn, delay_slots, repeat_slot);
}

static int validate_instruction_cpu_requirements(tic54x_insn *insn)
{
  if ((insn->tm->flags & FL_LP) && cpu != V545LP && cpu != V546LP)
    {
      as_bad (_("Instruction '%s' requires an LP cpu version"), insn->tm->name);
      return 0;
    }
  return 1;
}

static int validate_instruction_addressing_mode(tic54x_insn *insn)
{
  if ((insn->tm->flags & FL_FAR) && amode != far_mode)
    {
      as_bad (_("Instruction '%s' requires far mode addressing"), insn->tm->name);
      return 0;
    }
  return 1;
}

static void handle_delay_slot_instruction(tic54x_insn *insn, int words, int *delay_slots)
{
  if (!*delay_slots)
    return;

  if (!validate_delay_slot_fit(words, delay_slots))
    return;

  if (insn->tm->flags & FL_BMASK)
    {
      as_warn (_("Instructions which cause PC discontinuity are not "
                 "allowed in a delay slot. "
                 "Resulting behavior is undefined."));
    }
  *delay_slots -= words;
}

static int validate_delay_slot_fit(int words, int *delay_slots)
{
  if (*delay_slots != 0 && words > *delay_slots)
    {
      const char *msg_single = "Instruction does not fit in available "
                               "delay slots (%d-word insn, %d slot left)";
      const char *msg_multiple = "Instruction does not fit in available "
                                 "delay slots (%d-word insn, %d slots left)";
      
      if (input_line_pointer == savedp)
        {
          as_bad (ngettext (msg_single, msg_multiple, *delay_slots),
                  words, *delay_slots);
        }
      else
        {
          as_warn (ngettext (msg_single ". Resulting behavior is undefined.",
                            msg_multiple ". Resulting behavior is undefined.",
                            *delay_slots),
                   words, *delay_slots);
        }
      *delay_slots = 0;
      return 0;
    }
  if (*delay_slots != 0)
    *delay_slots -= words;
  return 1;
}

static void handle_repeat_slot_instruction(tic54x_insn *insn, int *repeat_slot)
{
  if (!*repeat_slot)
    return;

  if (insn->tm->flags & FL_NR)
    {
      as_warn (_("'%s' is not repeatable. "
                 "Resulting behavior is undefined."),
               insn->tm->name);
    }
  else if (insn->is_lkaddr)
    {
      as_warn (_("Instructions using long offset modifiers or absolute "
                 "addresses are not repeatable. "
                 "Resulting behavior is undefined."));
    }
  *repeat_slot = 0;
}

static void update_instruction_state_flags(tic54x_insn *insn, int *delay_slots, int *repeat_slot)
{
  if (insn->tm->flags & B_REPEAT)
    {
      *repeat_slot = 1;
    }
  if (insn->tm->flags & FL_DELAY)
    {
      *delay_slots = 2;
    }
}

/* Do a final adjustment on the symbol table; in this case, make sure we have
   a ".file" symbol.  */

void
tic54x_adjust_symtab (void)
{
  if (symbol_rootP == NULL
      || S_GET_STORAGE_CLASS (symbol_rootP) != C_FILE)
    {
      unsigned lineno;
      const char * filename = as_where (&lineno);
      c_dot_file_symbol (filename);
    }
}

/* In order to get gas to ignore any | chars at the start of a line,
   this function returns true if a | is found in a line.
   This lets us process parallel instructions, which span two lines.  */

int tic54x_unrecognized_line(int c)
{
    return c == PARALLEL_SEPARATOR;
}

/* Watch for local labels of the form $[0-9] and [_a-zA-Z][_a-zA-Z0-9]*?
   Encode their names so that only we see them and can map them to the
   appropriate places.
   FIXME -- obviously this isn't done yet.  These locals still show up in the
   symbol table.  */
void
tic54x_define_label (symbolS *sym)
{
  last_label_seen = sym;
}

/* Try to parse something that normal parsing failed at.  */

symbolS *
tic54x_undefined_symbol (char *name)
{
  tic54x_symbol *sym = find_symbol_in_hashes(name);
  
  if (sym != NULL || is_predefined_symbol(name))
    {
      return symbol_new (name, reg_section, &zero_address_frag,
			 sym ? sym->value : 0);
    }

  return NULL;
}

static tic54x_symbol *
find_symbol_in_hashes(char *name)
{
  tic54x_symbol *sym;
  
  if ((sym = str_hash_find (cc_hash, name)) != NULL)
    return sym;
  if ((sym = str_hash_find (cc2_hash, name)) != NULL)
    return sym;
  if ((sym = str_hash_find (cc3_hash, name)) != NULL)
    return sym;
  if ((sym = str_hash_find (sbit_hash, name)) != NULL)
    return sym;
  if ((sym = str_hash_find (reg_hash, name)) != NULL)
    return sym;
  if ((sym = str_hash_find (mmreg_hash, name)) != NULL)
    return sym;
    
  return NULL;
}

static int
is_predefined_symbol(char *name)
{
  return str_hash_find (misc_symbol_hash, name) != NULL ||
         !strcasecmp (name, "a") ||
         !strcasecmp (name, "b");
}

/* Parse a name in an expression before the expression parser takes a stab at
   it.  */

int
tic54x_parse_name (char *name ATTRIBUTE_UNUSED,
		   expressionS *expn ATTRIBUTE_UNUSED)
{
  return 0;
}

const char *
md_atof (int type, char *literalP, int *sizeP)
{
  const bool BIG_WORDIAN_FLOAT_STORAGE = true;
  return ieee_md_atof (type, literalP, sizeP, BIG_WORDIAN_FLOAT_STORAGE);
}

arelent *
tc_gen_reloc (asection *section, fixS *fixP)
{
  arelent *rel = allocate_relocation();
  asymbol *sym = symbol_get_bfdsym (fixP->fx_addsy);
  
  setup_relocation_symbol(rel, sym);
  setup_relocation_address(rel, fixP);
  setup_relocation_howto(rel, fixP, section, sym);
  
  if (!rel->howto)
    {
      handle_missing_howto(fixP);
      return NULL;
    }
  return rel;
}

static arelent *
allocate_relocation(void)
{
  return notes_alloc(sizeof(arelent));
}

static void
setup_relocation_symbol(arelent *rel, asymbol *sym)
{
  rel->sym_ptr_ptr = notes_alloc(sizeof(asymbol *));
  *rel->sym_ptr_ptr = sym;
}

static void
setup_relocation_address(arelent *rel, fixS *fixP)
{
  rel->address = fixP->fx_frag->fr_address + fixP->fx_where;
  rel->address /= OCTETS_PER_BYTE;
}

static void
setup_relocation_howto(arelent *rel, fixS *fixP, asection *section, asymbol *sym)
{
  bfd_reloc_code_real_type code = fixP->fx_r_type;
  rel->howto = bfd_reloc_type_lookup(stdoutput, code);
  
  if (!strcmp(sym->name, section->name))
    rel->howto += HOWTO_BANK;
}

static void
handle_missing_howto(fixS *fixP)
{
  const char *name = S_GET_NAME(fixP->fx_addsy);
  if (name == NULL)
    name = "<unknown>";
  
  bfd_reloc_code_real_type code = fixP->fx_r_type;
  as_fatal("Cannot generate relocation type for symbol %s, code %s",
           name, bfd_get_reloc_code_name(code));
}

/* Handle cons expressions.  */

void
tic54x_cons_fix_new (fragS *frag, int where, int octets, expressionS *expn,
		     bfd_reloc_code_real_type r)
{
  r = determine_relocation_type(octets);
  fix_new_exp (frag, where, octets, expn, 0, r);
}

static bfd_reloc_code_real_type
determine_relocation_type(int octets)
{
  const int OCTETS_WORD = 2;
  const int OCTETS_LONG = 4;
  
  if (octets == OCTETS_WORD)
    return BFD_RELOC_TIC54X_16_OF_23;
  
  if (octets == OCTETS_LONG)
    return get_long_relocation_type();
  
  as_bad (_("Unsupported relocation size %d"), octets);
  return BFD_RELOC_TIC54X_16_OF_23;
}

static bfd_reloc_code_real_type
get_long_relocation_type(void)
{
  if (emitting_long)
    return BFD_RELOC_TIC54X_23;
  
  return BFD_RELOC_32;
}

/* Attempt to simplify or even eliminate a fixup.
   To indicate that a fixup has been eliminated, set fixP->fx_done.

   If fixp->fx_addsy is non-NULL, we'll have to generate a reloc entry.   */

void
md_apply_fix (fixS *fixP, valueT *valP, segT seg ATTRIBUTE_UNUSED)
{
  char *buf = fixP->fx_where + fixP->fx_frag->fr_literal;
  valueT val = * valP;

  switch (fixP->fx_r_type)
    {
    default:
      as_fatal ("Bad relocation type: 0x%02x", fixP->fx_r_type);
      return;
    case BFD_RELOC_TIC54X_MS7_OF_23:
      val = (val >> 16) & 0x7F;
      /* Fall through.  */
    case BFD_RELOC_TIC54X_16_OF_23:
    case BFD_RELOC_16:
      apply_16bit_relocation(buf, val, valP);
      break;
    case BFD_RELOC_TIC54X_PARTLS7:
      apply_partls7_relocation(buf, val, valP);
      break;
    case BFD_RELOC_TIC54X_PARTMS9:
      apply_partms9_relocation(buf, val);
      break;
    case BFD_RELOC_32:
    case BFD_RELOC_TIC54X_23:
      apply_32bit_relocation(buf, val);
      break;
    }

  mark_fixup_done_if_resolved(fixP);
}

static void
apply_16bit_relocation(char *buf, valueT val, valueT *valP)
{
  #define MASK_16BIT 0xFFFF
  bfd_put_16 (stdoutput, val, buf);
  *valP = val & MASK_16BIT;
}

static void
apply_partls7_relocation(char *buf, valueT val, valueT *valP)
{
  #define MASK_7BIT 0x7F
  #define MASK_PARTLS7 0xFF80
  bfd_vma existing = bfd_get_16 (stdoutput, buf);
  bfd_put_16 (stdoutput, (existing & MASK_PARTLS7) | (val & MASK_7BIT), buf);
  *valP = val & MASK_7BIT;
}

static void
apply_partms9_relocation(char *buf, valueT val)
{
  #define MASK_PARTMS9 0xFE00
  #define SHIFT_PARTMS9 7
  bfd_vma existing = bfd_get_16 (stdoutput, buf);
  bfd_put_16 (stdoutput, (existing & MASK_PARTMS9) | (val >> SHIFT_PARTMS9), buf);
}

static void
apply_32bit_relocation(char *buf, valueT val)
{
  #define MASK_23BIT 0xFF800000
  bfd_vma existing = bfd_get_32 (stdoutput, buf);
  bfd_put_32 (stdoutput, (existing & MASK_23BIT) | val, buf);
}

static void
mark_fixup_done_if_resolved(fixS *fixP)
{
  if (fixP->fx_addsy == NULL && fixP->fx_pcrel == 0)
    fixP->fx_done = 1;
}

/* This is our chance to record section alignment
   don't need to do anything here, since BFD does the proper encoding.  */

valueT
md_section_align (segT segment ATTRIBUTE_UNUSED, valueT section_size)
{
  return section_size;
}

long
md_pcrel_from (fixS *fixP ATTRIBUTE_UNUSED)
{
  return 0;
}

/* Mostly little-endian, but longwords (4 octets) get MS word stored
   first.  */

void
tic54x_number_to_chars (char *buf, valueT val, int n)
{
  const int WORD_SIZE = 4;
  const int HALF_WORD_SIZE = 2;
  const valueT LOWER_HALF_MASK = 0xFFFF;
  const int UPPER_HALF_SHIFT = 16;

  if (n != WORD_SIZE)
    {
      number_to_chars_littleendian (buf, val, n);
      return;
    }

  valueT upper_half = val >> UPPER_HALF_SHIFT;
  valueT lower_half = val & LOWER_HALF_MASK;
  
  number_to_chars_littleendian (buf, upper_half, HALF_WORD_SIZE);
  number_to_chars_littleendian (buf + HALF_WORD_SIZE, lower_half, HALF_WORD_SIZE);
}

int tic54x_estimate_size_before_relax(fragS *frag ATTRIBUTE_UNUSED,
                                       segT seg ATTRIBUTE_UNUSED)
{
    return 0;
}

/* We use this to handle bit allocations which we couldn't handle before due
   to symbols being in different frags.  return number of octets added.  */

int
tic54x_relax_frag (fragS *frag, long stretch ATTRIBUTE_UNUSED)
{
  symbolS *sym = frag->fr_symbol;
  int growth = 0;

  if (sym == NULL)
    return growth;

  struct bit_info *bi = (struct bit_info *) frag->fr_opcode;
  int bit_offset = frag_bit_offset (frag_prev (frag, bi->seg), bi->seg);
  int size = S_GET_VALUE (sym);
  fragS *prev_frag = bit_offset_frag (frag_prev (frag, bi->seg), bi->seg);
  int available = 16 - bit_offset;

  if (symbol_get_frag (sym) != &zero_address_frag
      || S_IS_COMMON (sym)
      || !S_IS_DEFINED (sym))
    as_bad_where (frag->fr_file, frag->fr_line,
                  _("non-absolute value used with .space/.bes"));

  if (size < 0)
    {
      const char *type_name = bi->type == TYPE_SPACE ? ".space" :
                             bi->type == TYPE_BES ? ".bes" : ".field";
      as_warn (_("negative value ignored in %s"), type_name);
      growth = 0;
      frag->tc_frag_data = frag->fr_fix = 0;
      goto cleanup;
    }

  if (bi->type == TYPE_FIELD)
    growth = handle_field_type(frag, bi, prev_frag, bit_offset, available, size);
  else
    growth = handle_space_or_bes_type(frag, bi, prev_frag, bit_offset, available, size);

cleanup:
  frag->fr_symbol = 0;
  frag->fr_opcode = 0;
  free ((void *) bi);
  return growth;
}

static int
handle_field_type(fragS *frag, struct bit_info *bi, fragS *prev_frag, 
                  int bit_offset, int available, int size)
{
  if (bit_offset != 0 && available >= size)
    {
      write_field_to_prev_frag(prev_frag, bi, available, size);
      return clear_current_frag(frag);
    }
  else
    {
      write_field_to_current_frag(frag, bi, size);
      return 0;
    }
}

static void
write_field_to_prev_frag(fragS *prev_frag, struct bit_info *bi, int available, int size)
{
  char *p = prev_frag->fr_literal;
  valueT value = bi->value;
  value <<= available - size;
  value |= ((uint16_t) p[1] << 8) | p[0];
  md_number_to_chars (p, value, 2);
  update_frag_data(prev_frag, size);
  if (bi->sym)
    symbol_set_frag (bi->sym, prev_frag);
}

static void
write_field_to_current_frag(fragS *frag, struct bit_info *bi, int size)
{
  char *p = frag->fr_literal;
  valueT value = bi->value << (16 - size);
  md_number_to_chars (p, value, 2);
  frag->tc_frag_data = (size == 16) ? 0 : size;
}

static int
handle_space_or_bes_type(fragS *frag, struct bit_info *bi, fragS *prev_frag,
                         int bit_offset, int available, int size)
{
  int growth;
  
  if (bit_offset != 0 && bit_offset < 16)
    {
      if (available >= size)
        {
          update_frag_data(prev_frag, size);
          if (bi->sym)
            symbol_set_frag (bi->sym, prev_frag);
          return clear_current_frag(frag);
        }
      if (bi->type == TYPE_SPACE && bi->sym)
        symbol_set_frag (bi->sym, prev_frag);
      size -= available;
    }
  
  growth = calculate_growth(size, frag->fr_fix);
  initialize_frag_literal(frag, growth);
  frag->fr_fix = growth;
  frag->tc_frag_data = size % 16;
  
  if (bi->type == TYPE_BES && bi->sym)
    S_SET_VALUE (bi->sym, frag->fr_fix / OCTETS_PER_BYTE - 1);
  
  return growth;
}

static int
clear_current_frag(fragS *frag)
{
  int growth = -frag->fr_fix;
  frag->fr_fix = 0;
  frag->tc_frag_data = 0;
  return growth;
}

static void
update_frag_data(fragS *frag, int size)
{
  frag->tc_frag_data += size;
  if (frag->tc_frag_data == 16)
    frag->tc_frag_data = 0;
}

static int
calculate_growth(int size, int fr_fix)
{
  return (size + 15) / 16 * OCTETS_PER_BYTE - fr_fix;
}

static void
initialize_frag_literal(fragS *frag, int growth)
{
  int i;
  for (i = 0; i < growth; i++)
    frag->fr_literal[i] = 0;
}

void
tic54x_convert_frag (bfd *abfd ATTRIBUTE_UNUSED,
		     segT seg ATTRIBUTE_UNUSED,
		     fragS *frag)
{
  frag->fr_offset = (frag->fr_next->fr_address
		     - frag->fr_address
		     - frag->fr_fix) / frag->fr_var;
  if (frag->fr_offset < 0)
    {
      as_bad_where (frag->fr_file, frag->fr_line,
		    _("attempt to .space/.bes backwards? (%ld)"),
		    (long) frag->fr_offset);
    }
  frag->fr_type = rs_space;
}

/* We need to avoid having labels defined for certain directives/pseudo-ops
   since once the label is defined, it's in the symbol table for good.  TI
   syntax puts the symbol *before* the pseudo (which is kinda like MRI syntax,
   I guess, except I've never seen a definition of MRI syntax).

   Don't allow labels to start with '.'  */

int
tic54x_start_label (char * label_start, int nul_char, int next_char)
{
  char *rest;

  if (current_stag != NULL)
    return 0;

  if (next_char != ':' && *label_start == '.')
    {
      as_bad (_("Invalid label '%s'"), label_start);
      return 0;
    }

  if (is_end_of_stmt (next_char))
    return 1;

  rest = input_line_pointer;
  if (nul_char == '"')
    ++rest;
  
  while (is_whitespace (next_char))
    next_char = *++rest;
  
  if (next_char != '.')
    return 1;

  return !is_reserved_directive(rest);
}

static int
is_reserved_directive(const char *rest)
{
  return is_directive_match(rest, ".tag", 4) ||
         is_directive_match(rest, ".struct", 7) ||
         is_directive_match(rest, ".union", 6) ||
         is_directive_match(rest, ".macro", 6) ||
         is_directive_match(rest, ".set", 4) ||
         is_directive_match(rest, ".equ", 4);
}

static int
is_directive_match(const char *rest, const char *directive, int len)
{
  return strncasecmp(rest, directive, len) == 0 && is_whitespace(rest[len]);
}
