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


void md_show_usage(FILE *stream)
{
  if (!stream)
    return;
  fprintf(stream, _("C54x-specific command line options:\n"));
  fprintf(stream, _("-mfar-mode | -mf          Use extended addressing\n"));
  fprintf(stream, _("-mcpu=<CPU version>       Specify the CPU version\n"));
  fprintf(stream, _("-merrors-to-file <filename>\n"));
  fprintf(stream, _("-me <filename>            Redirect errors to a file\n"));
}

/* Output a single character (upper octet is zero).  */

static void tic54x_emit_char(char c) {
    expressionS expn = {0};
    expn.X_op = O_constant;
    expn.X_add_number = (unsigned char)c;
    emit_expr(&expn, 2);
}

/* Walk backwards in the frag chain.  */

static fragS *
frag_prev(fragS *frag, segT seg)
{
    segment_info_type *seginfo;
    frchainS *frchain;
    fragS *fragp;

    if (!frag || !seg)
        return NULL;

    seginfo = seg_info(seg);
    if (!seginfo)
        return NULL;

    frchain = seginfo->frchainP;
    if (!frchain)
        return NULL;

    for (fragp = frchain->frch_root; fragp; fragp = fragp->fr_next) {
        if (fragp->fr_next == frag)
            return fragp;
    }

    return NULL;
}

static fragS *
bit_offset_frag(fragS *frag, segT seg)
{
    while (frag)
    {
        if (frag->fr_fix != 0 || frag->fr_opcode != NULL || frag->tc_frag_data != 0)
            return frag;
        frag = frag_prev(frag, seg);
    }
    return NULL;
}

/* Return the number of bits allocated in the most recent word, or zero if
   none. .field/.space/.bes may leave words partially allocated.  */

static int frag_bit_offset(fragS *frag, segT seg) {
    fragS *offset_frag = bit_offset_frag(frag, seg);
    if (!offset_frag)
        return 0;
    if (offset_frag->fr_opcode)
        return -1;
    return offset_frag->tc_frag_data;
}

/* Read an expression from a C string; returns a pointer past the end of the
   expression.  */

static char *parse_expression(char *str, expressionS *expn)
{
    char *saved_input = input_line_pointer;
    input_line_pointer = str;
    expression(expn);
    char *parse_end = input_line_pointer;
    input_line_pointer = saved_input;
    return parse_end;
}

/* .asg "character-string"|character-string, symbol

   .eval is the only pseudo-op allowed to perform arithmetic on substitution
   symbols.  all other use of symbols defined with .asg are currently
   unsupported.  */

static void tic54x_asg(int x ATTRIBUTE_UNUSED)
{
    int c;
    char *name = NULL;
    char *str = NULL;
    int quoted = (*input_line_pointer == '"');

    ILLEGAL_WITHIN_STRUCT();

    if (quoted) {
        int len = 0;
        str = demand_copy_C_string(&len);
        c = *input_line_pointer;
    } else {
        size_t len = 0;
        char *start = input_line_pointer;
        while ((c = *input_line_pointer) != ',') {
            if (is_end_of_stmt(c))
                break;
            ++input_line_pointer;
        }
        len = input_line_pointer - start;
        str = notes_memdup(start, len, len + 1);
        if (str)
            str[len] = '\0';
    }

    if (c != ',') {
        as_bad(_("Comma and symbol expected for '.asg STRING, SYMBOL'"));
        notes_free(str);
        ignore_rest_of_line();
        return;
    }

    ++input_line_pointer;
    c = get_symbol_name(&name);
    if (!name) {
        as_bad(_("Failed to get symbol name for '.asg STRING, SYMBOL'"));
        notes_free(str);
        ignore_rest_of_line();
        return;
    }
    {
        char *tmp = notes_strdup(name);
        if (!tmp) {
            as_bad(_("Out of memory for symbol name"));
            notes_free(str);
            ignore_rest_of_line();
            return;
        }
        name = tmp;
    }
    (void) restore_line_pointer(c);

    if (!ISALPHA(*name)) {
        as_bad(_("symbols assigned with .asg must begin with a letter"));
        notes_free(str);
        notes_free(name);
        ignore_rest_of_line();
        return;
    }

    subsym_create_or_replace(name, str);
    notes_free(name);
    demand_empty_rest_of_line();
    notes_free(str);
}

/* .eval expression, symbol
   There's something screwy about this.  The other assembler sometimes does and
   sometimes doesn't substitute symbols defined with .eval.
   We'll put the symbols into the subsym table as well as the normal symbol
   table, since that's what works best.  */

static void tic54x_eval(int x ATTRIBUTE_UNUSED)
{
    char c;
    int value;
    char *name = NULL;
    symbolS *symbolP = NULL;
    char valuestr[32];
    char *tmp = NULL;
    int quoted;

    ILLEGAL_WITHIN_STRUCT();

    SKIP_WHITESPACE();

    quoted = (*input_line_pointer == '"') ? 1 : 0;
    if (quoted)
        ++input_line_pointer;
    value = get_absolute_expression();
    if (quoted) {
        if (*input_line_pointer != '"') {
            as_bad(_("Unterminated string after absolute expression"));
            ignore_rest_of_line();
            return;
        }
        ++input_line_pointer;
    }
    if (*input_line_pointer != ',') {
        as_bad(_("Comma and symbol expected for '.eval EXPR, SYMBOL'"));
        ignore_rest_of_line();
        return;
    }
    ++input_line_pointer;

    c = get_symbol_name(&name);

    if (!ISALPHA(*name)) {
        as_bad(_("symbols assigned with .eval must begin with a letter"));
        restore_line_pointer(c);
        ignore_rest_of_line();
        return;
    }
    name = notes_strdup(name);
    restore_line_pointer(c);

    symbolP = symbol_new(name, absolute_section, &zero_address_frag, value);
    if (!symbolP) {
        as_bad(_("Failed to create symbol for .eval"));
        ignore_rest_of_line();
        return;
    }
    SF_SET_LOCAL(symbolP);
    symbol_table_insert(symbolP);

    snprintf(valuestr, sizeof(valuestr), "%d", value);
    tmp = notes_strdup(valuestr);
    if (!tmp) {
        as_bad(_("Memory allocation failure in .eval"));
        ignore_rest_of_line();
        return;
    }
    subsym_create_or_replace(name, tmp);

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

static void tic54x_bss(int x ATTRIBUTE_UNUSED)
{
    char c;
    char *name;
    char *p;
    offsetT words;
    segT current_seg;
    subsegT current_subseg;
    symbolS *symbolP;
    int block = 0;
    int align = 0;

    ILLEGAL_WITHIN_STRUCT();

    current_seg = now_seg;
    current_subseg = now_subseg;

    c = get_symbol_name(&name);
    if (c == '"') {
        c = *++input_line_pointer;
    }
    if (c != ',') {
        as_bad(_(".bss size argument missing\n"));
        ignore_rest_of_line();
        return;
    }

    ++input_line_pointer;
    words = get_absolute_expression();
    if (words < 0) {
        as_bad(_(".bss size %d < 0!"), (int)words);
        ignore_rest_of_line();
        return;
    }

    if (*input_line_pointer == ',') {
        ++input_line_pointer;

        if (*input_line_pointer != ',') {
            block = get_absolute_expression();
        } else {
            block = 0;
        }

        if (*input_line_pointer == ',') {
            ++input_line_pointer;
            align = get_absolute_expression();
        } else {
            align = 0;
        }
    } else {
        block = 0;
        align = 0;
    }

    subseg_set(bss_section, 0);

    symbolP = symbol_find_or_make(name);
    if (!symbolP) {
        as_bad(_("Failed to create/fetch symbol for .bss\n"));
        subseg_set(current_seg, current_subseg);
        ignore_rest_of_line();
        return;
    }

    if (S_GET_SEGMENT(symbolP) == bss_section) {
        symbolS *frag_sym = symbol_get_frag(symbolP);
        if (frag_sym)
            frag_sym->fr_symbol = NULL;
    }

    symbol_set_frag(symbolP, frag_now);
    p = frag_var(rs_org, 1, 1, 0, symbolP, words * OCTETS_PER_BYTE, NULL);
    if (p)
        *p = 0;

    S_SET_SEGMENT(symbolP, bss_section);

    if (S_GET_STORAGE_CLASS(symbolP) != C_EXT)
        S_SET_STORAGE_CLASS(symbolP, C_STAT);

    if (align) {
        s_align_bytes(4);
        if (input_line_pointer > buffer)
            --input_line_pointer;
    }

    if (block)
        bss_section->flags |= SEC_TIC54X_BLOCK;

    subseg_set(current_seg, current_subseg);
    demand_empty_rest_of_line();
}


static void stag_add_field_symbols(struct stag *stag,
                                   const char *path,
                                   bfd_vma base_offset,
                                   symbolS *rootsym,
                                   const char *root_stag_name)
{
    if (!stag || !root_stag_name) {
        return;
    }

    char *prefix = NULL;
    if (!path) {
        prefix = concat("", "", (const char *) NULL);
    } else {
        prefix = concat(path, *path ? "." : "", (const char *) NULL);
    }
    if (!prefix) {
        return;
    }

    for (struct stag_field *field = stag->field; field; field = field->next) {
        char *name = NULL;
        if (!field->name) {
            continue;
        }
        name = concat(prefix, field->name, (const char *) NULL);
        if (!name) {
            continue;
        }
        int free_name = 1;

        if (!rootsym) {
            bfd_vma offset = (field->stag ? field->offset : base_offset + field->offset);

            symbolS *sym = symbol_new(name, absolute_section, &zero_address_frag, offset);
            if (sym) {
                SF_SET_LOCAL(sym);
                symbol_table_insert(sym);
            }
        } else {
            subsym_ent_t *ent = (subsym_ent_t *) xmalloc(sizeof(*ent));
            if (!ent) {
                free(name);
                continue;
            }
            const char *root_name = S_GET_NAME(rootsym);
            if (!root_name) {
                free(ent);
                free(name);
                continue;
            }
            ent->u.s = concat(root_name, "+", root_stag_name,
                              name + strlen(root_name),
                              (const char *) NULL);
            if (!ent->u.s) {
                free(ent);
                free(name);
                continue;
            }
            ent->freekey = 1;
            ent->freeval = 1;
            ent->isproc = 0;
            ent->ismath = 0;
            str_hash_insert(subsym_hash[0], name, ent, 0);
            free_name = 0;
        }

        if (field->stag) {
            stag_add_field_symbols(field->stag, name, field->offset, rootsym, root_stag_name);
        }

        if (free_name) {
            free(name);
        }
    }

    free(prefix);
}

/* Keep track of stag fields so that when structures are nested we can add the
   complete dereferencing symbols to the symbol table.  */

static void stag_add_field(struct stag *parent, const char *name, bfd_vma offset, struct stag *stag) {
    if (!parent || !name) {
        return;
    }

    struct stag_field *sfield = XCNEW(struct stag_field);
    if (!sfield) {
        return;
    }

    sfield->name = xstrdup(name);
    if (!sfield->name) {
        free(sfield);
        return;
    }
    sfield->offset = offset;
    sfield->bitfield_offset = parent->current_bitfield_offset;
    sfield->stag = stag;
    sfield->next = NULL;

    if (!parent->field) {
        parent->field = sfield;
    } else {
        struct stag_field *sf = parent->field;
        while (sf->next) {
            sf = sf->next;
        }
        sf->next = sfield;
    }

    if (parent->name && startswith(parent->name, ".fake")) {
        symbolS *sym = symbol_new(name, absolute_section, &zero_address_frag, offset);
        if (sym) {
            SF_SET_LOCAL(sym);
            symbol_table_insert(sym);
        }
    }
}

/* [STAG] .struct       [OFFSET]
   Start defining structure offsets (symbols in absolute section).  */

static void tic54x_struct(int arg) {
    int start_offset = 0;
    int is_union = arg;

    if (!current_stag) {
        stag_saved_seg = now_seg;
        stag_saved_subseg = now_subseg;
        subseg_set(absolute_section, 0);
    } else if (current_stag->current_bitfield_offset != 0) {
        ++abs_section_offset;
        current_stag->current_bitfield_offset = 0;
    }

    if (!is_union) {
        SKIP_WHITESPACE();
        if (!is_end_of_stmt(*input_line_pointer)) {
            start_offset = get_absolute_expression();
        } else {
            start_offset = 0;
        }
    }

    if (current_stag) {
        struct stag *new_stag = XCNEW(struct stag);
        new_stag->outer = current_stag;
        current_stag->inner = new_stag;
        current_stag = new_stag;
        if (start_offset) {
            as_warn(_("Offset on nested structures is ignored"));
        }
        start_offset = abs_section_offset;
    } else {
        current_stag = XCNEW(struct stag);
        abs_section_offset = start_offset;
    }
    current_stag->is_union = is_union;

    if (line_label == NULL) {
        static int struct_count = 0;
        char fake[32];
        if (snprintf(fake, sizeof(fake), ".fake_stag%d", struct_count++) >= (int)sizeof(fake)) {
            struct_count--;
            as_warn(_("Fake stag label truncated"));
            fake[sizeof(fake)-1] = '\0';
        }
        current_stag->sym = symbol_new(fake, absolute_section, &zero_address_frag, abs_section_offset);
    } else {
        char *label = xstrdup(S_GET_NAME(line_label));
        if (label == NULL) {
            as_warn(_("Failed to allocate memory for label"));
            return;
        }
        current_stag->sym = symbol_new(label, absolute_section, &zero_address_frag, abs_section_offset);
        free(label);
    }
    current_stag->name = S_GET_NAME(current_stag->sym);
    SF_SET_LOCAL(current_stag->sym);

    if (current_stag->outer == NULL) {
        symbol_table_insert(current_stag->sym);
    }

    line_label = NULL;
}

/* [LABEL] .endstruct
   finish defining structure offsets; optional LABEL's value will be the size
   of the structure.  */

static void tic54x_endstruct(int is_union) {
    int size;
    const char *path;

    if (!current_stag) {
        as_bad(_(".end%s without preceding .%s"),
               is_union ? "union" : "struct",
               is_union ? "union" : "struct");
        ignore_rest_of_line();
        return;
    }

    if (current_stag->is_union != is_union) {
        as_bad(_(".end%s without preceding .%s"),
               is_union ? "union" : "struct",
               is_union ? "union" : "struct");
        ignore_rest_of_line();
        return;
    }

    path = (startswith(current_stag->name, ".fake")) ? "" : current_stag->name;

    if (current_stag->current_bitfield_offset) {
        ++abs_section_offset;
        current_stag->current_bitfield_offset = 0;
    }

    size = current_stag->is_union
        ? current_stag->size
        : abs_section_offset - S_GET_VALUE(current_stag->sym);

    if (line_label) {
        S_SET_VALUE(line_label, size);
        symbol_table_insert(line_label);
        line_label = NULL;
    }

    if (!current_stag->is_union)
        current_stag->size = size;

    if (!current_stag->outer) {
        str_hash_insert(stag_hash, current_stag->name, current_stag, 0);
        stag_add_field_symbols(current_stag, path, S_GET_VALUE(current_stag->sym), NULL, NULL);
    }

    current_stag = current_stag->outer;

    if (current_stag) {
        if (current_stag->inner && current_stag->inner->name && current_stag->inner->sym) {
            stag_add_field(current_stag, current_stag->inner->name,
                           S_GET_VALUE(current_stag->inner->sym),
                           current_stag->inner);
        }
    } else {
        subseg_set(stag_saved_seg, stag_saved_subseg);
    }
}

/* [LABEL]      .tag    STAG
   Reference a structure within a structure, as a sized field with an optional
   label.
   If used outside of a .struct/.endstruct, overlays the given structure
   format on the existing allocated space.  */

static void tic54x_tag(int ignore ATTRIBUTE_UNUSED)
{
    char *name = NULL;
    int c = get_symbol_name(&name);
    struct stag *stag = str_hash_find(stag_hash, name);

    if (!stag) {
        if (name && *name)
            as_bad(_("Unrecognized struct/union tag '%s'"), name);
        else
            as_bad(_(".tag requires a structure tag"));
        ignore_rest_of_line();
        return;
    }

    if (line_label == NULL) {
        as_bad(_("Label required for .tag"));
        ignore_rest_of_line();
        return;
    }

    char *label = xstrdup(S_GET_NAME(line_label));
    if (!label) {
        as_bad(_("Memory allocation failed for tag label"));
        ignore_rest_of_line();
        return;
    }

    if (current_stag != NULL) {
        stag_add_field(
            current_stag,
            label,
            abs_section_offset - S_GET_VALUE(current_stag->sym),
            stag
        );
    } else {
        symbolS *sym = symbol_find(label);

        if (!sym) {
            as_bad(_(".tag target '%s' undefined"), label);
            ignore_rest_of_line();
            free(label);
            return;
        }
        stag_add_field_symbols(
            stag,
            S_GET_NAME(sym),
            S_GET_VALUE(stag->sym),
            sym,
            stag->name
        );
    }
    free(label);

    if (current_stag != NULL && !current_stag->is_union)
        abs_section_offset += stag->size;

    restore_line_pointer(c);
    demand_empty_rest_of_line();
    line_label = NULL;
}


/* Handle all .byte, .char, .double, .field, .float, .half, .int, .long,
   .short, .string, .ubyte, .uchar, .uhalf, .uint, .ulong, .ushort, .uword,
   and .word.  */

static void tic54x_struct_field(int type)
{
    unsigned int size = 0;
    int count = 1;
    int new_bitfield_offset = 0;
    int needs_field_align = current_stag->current_bitfield_offset != 0;
    int needs_longword_align = 0;

    SKIP_WHITESPACE();
    if (!is_end_of_stmt(*input_line_pointer))
        count = get_absolute_expression();

    switch (type) {
        case 'b': case 'B': case 'c': case 'C':
        case 'h': case 'H': case 'i': case 'I':
        case 's': case 'S': case 'w': case 'W': case '*':
            size = 1;
            break;
        case 'f': case 'l': case 'L':
            size = 2;
            needs_longword_align = 1;
            break;
        case '.':
            if (count < 1 || count > 32) {
                as_bad(_(".field count '%d' out of range (1 <= X <= 32)"), count);
                ignore_rest_of_line();
                return;
            }
            if (current_stag->current_bitfield_offset + count > 16) {
                if (count == 32) {
                    size = 2;
                    count = 1;
                } else if (count > 16) {
                    size = 1;
                    count = 1;
                    new_bitfield_offset = count - 16;
                } else {
                    new_bitfield_offset = count;
                }
            } else {
                needs_field_align = 0;
                new_bitfield_offset = current_stag->current_bitfield_offset + count;
            }
            break;
        default:
            as_bad(_("Unrecognized field type '%c'"), type);
            ignore_rest_of_line();
            return;
    }

    if (needs_field_align) {
        current_stag->current_bitfield_offset = 0;
        ++abs_section_offset;
    }
    if (needs_longword_align && (abs_section_offset & 0x1))
        ++abs_section_offset;

    if (line_label == NULL) {
        static int fieldno = 0;
        char fake[32];
        int res = snprintf(fake, sizeof(fake), ".fake_field%d", fieldno++);
        if (res < 0 || res >= (int)sizeof(fake)) {
            as_bad(_("Fake field label formatting error"));
            ignore_rest_of_line();
            return;
        }
        stag_add_field(current_stag, fake,
                       abs_section_offset - S_GET_VALUE(current_stag->sym),
                       NULL);
    } else {
        char *label = xstrdup(S_GET_NAME(line_label));
        if (!label) {
            as_bad(_("Memory allocation failed for label copy"));
            ignore_rest_of_line();
            return;
        }
        stag_add_field(current_stag, label,
                       abs_section_offset - S_GET_VALUE(current_stag->sym),
                       NULL);
        free(label);
    }

    if (current_stag->is_union) {
        unsigned int total = size * count;
        if (current_stag->size < total)
            current_stag->size = total;
    } else {
        abs_section_offset += size * count;
        current_stag->current_bitfield_offset = new_bitfield_offset;
    }
    line_label = NULL;
}

/* Handle .byte, .word. .int, .long and all variants.  */

static void tic54x_cons(int type) {
    unsigned int c;
    int octets;
    expressionS expn;
    offsetT value;

    if (current_stag != NULL) {
        tic54x_struct_field(type);
        return;
    }

#ifdef md_flush_pending_output
    md_flush_pending_output();
#endif

    generate_lineno_debug();

    if (type == 'l' || type == 'L') {
        frag_align(2, 0, 2);
        if (line_label != NULL) {
            symbol_set_frag(line_label, frag_now);
            S_SET_VALUE(line_label, frag_now_fix());
        }
    }

    switch (type) {
        case 'l':
        case 'L':
        case 'x':
            octets = 4;
            break;
        case 'b':
        case 'B':
        case 'c':
        case 'C':
            octets = 1;
            break;
        default:
            octets = 2;
            break;
    }

    do {
        if (*input_line_pointer == '"') {
            input_line_pointer++;
            while (is_a_char(c = next_char_of_string()))
                tic54x_emit_char(c);
            know(input_line_pointer[-1] == '\"');
        } else {
            input_line_pointer = parse_expression(input_line_pointer, &expn);
            if (expn.X_op == O_constant) {
                value = expn.X_add_number;
                if (octets == 1 && (value > 0xFF || value < -0x100))
                    as_warn(_("Overflow in expression, truncated to 8 bits"));
                else if (octets == 2 && (value > 0xFFFF || value < -0x10000))
                    as_warn(_("Overflow in expression, truncated to 16 bits"));
            }
            if (expn.X_op != O_constant && octets < 2) {
                as_bad(_("Relocatable values require at least WORD storage"));
                ignore_rest_of_line();
                return;
            }
            if (expn.X_op != O_constant && amode == c_mode && octets == 4) {
                amode = far_mode;
                emitting_long = 1;
                emit_expr(&expn, 4);
                emitting_long = 0;
                amode = c_mode;
            } else {
                emitting_long = (octets == 4);
                emit_expr(&expn, (octets == 1) ? 2 : octets);
                emitting_long = 0;
            }
        }
    } while (*input_line_pointer++ == ',');

    input_line_pointer--;
    demand_empty_rest_of_line();
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

void tic54x_global(int type) {
    char *name = NULL;
    int c = 0;
    symbolS *symbolP = NULL;

    if (type == 'r') {
        as_warn(_("Use of .def/.ref is deprecated.  Use .global instead"));
    }

    ILLEGAL_WITHIN_STRUCT();

    while (1) {
        c = get_symbol_name(&name);
        if (!name) {
            as_bad(_("Failed to get symbol name"));
            break;
        }
        symbolP = symbol_find_or_make(name);
        if (!symbolP) {
            as_bad(_("Failed to find or create symbol: %s"), name);
            break;
        }

        c = restore_line_pointer(c);
        S_SET_STORAGE_CLASS(symbolP, C_EXT);

        if (c != ',') {
            break;
        }

        input_line_pointer++;
        if (is_end_of_stmt(*input_line_pointer)) {
            c = *input_line_pointer;
            break;
        }
    }

    demand_empty_rest_of_line();
}

static void free_subsym_ent(void *ent) {
    if (!ent) return;

    string_tuple_t *tuple = (string_tuple_t *)ent;
    subsym_ent_t *val = (subsym_ent_t *)tuple->value;

    if (val) {
        if (val->freekey && tuple->key) {
            free((void *)tuple->key);
        }
        if (val->freeval && val->u.s) {
            free(val->u.s);
        }
        free(val);
    }
    free(tuple);
}

static htab_t subsym_htab_create(void)
{
    htab_t table = htab_create_alloc(16, hash_string_tuple, eq_string_tuple, free_subsym_ent, xcalloc, free);
    if (!table) {
        return NULL;
    }
    return table;
}

static void free_local_label_ent(void *ent)
{
    if (!ent)
        return;

    string_tuple_t *tuple = (string_tuple_t *)ent;

    free(tuple->key);
    free(tuple->value);
    free(ent);
}

static htab_t local_label_htab_create(void)
{
    return htab_create_alloc(
        16,
        hash_string_tuple,
        eq_string_tuple,
        free_local_label_ent,
        xcalloc,
        free
    );
}

/* Reset all local labels.  */

static void tic54x_clear_local_labels(void)
{
    htab_empty(local_label_hash[macro_level]);
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

static void tic54x_sect(int arg) {
    ILLEGAL_WITHIN_STRUCT();

    tic54x_clear_local_labels(0);

    if (arg == 't') {
        s_text(0);
        return;
    }
    if (arg == 'd') {
        s_data(0);
        return;
    }

    char *name = NULL;
    int len = 0;
    const char *flags = ",\"w\"\n";

    if (*input_line_pointer == '"') {
        name = demand_copy_C_string(&len);
        if (!name) {
            return;
        }
        demand_empty_rest_of_line();
        char *tmp = concat(name, flags, (char *)NULL);
        free(name);
        name = tmp;
        if (!name) {
            return;
        }
    } else {
        int c = get_symbol_name(&name);
        if (!name) {
            return;
        }
        char *tmp = concat(name, flags, (char *)NULL);
        free(name);
        name = tmp;
        if (!name) {
            return;
        }
        (void)restore_line_pointer(c);
        demand_empty_rest_of_line();
    }

    input_scrub_insert_line(name);
    free(name);

    obj_coff_section(0);

    if (line_label != NULL) {
        S_SET_SEGMENT(line_label, now_seg);
        symbol_set_frag(line_label, frag_now);
        S_SET_VALUE(line_label, frag_now_fix());
        if (S_GET_STORAGE_CLASS(line_label) != C_EXT) {
            S_SET_STORAGE_CLASS(line_label, C_LABEL);
        }
    }
}

/* [symbol] .space space_in_bits
   [symbol] .bes space_in_bits
   BES puts the symbol at the *last* word allocated

   cribbed from s_space.  */

static void tic54x_space(int arg) {
    expressionS expn;
    char *p = NULL;
    int octets = 0;
    long words;
    int bits_per_byte = (OCTETS_PER_BYTE * 8);
    int bit_offset = 0;
    symbolS *label = line_label;
    int bes = arg;

    ILLEGAL_WITHIN_STRUCT();

#ifdef md_flush_pending_output
    md_flush_pending_output();
#endif

    expression(&expn);

    if (expn.X_op != O_constant || frag_bit_offset(frag_now, now_seg) == -1) {
        struct bit_info *bi = XNEW(struct bit_info);
        if (!bi)
            return;
        bi->seg = now_seg;
        bi->type = bes;
        bi->sym = label;
        p = frag_var(rs_machine_dependent, 65536 * 2, 1, 0,
                     make_expr_symbol(&expn), 0, (char *)bi);
        if (p)
            *p = 0;
        return;
    }

    bit_offset = frag_now->tc_frag_data;
    if (bit_offset > 0 && bit_offset < 16) {
        int spare_bits = bits_per_byte - bit_offset;

        if (spare_bits >= expn.X_add_number) {
            if (label) {
                symbol_set_frag(label, frag_now);
                S_SET_VALUE(label, frag_now_fix() - 1);
                label = NULL;
            }
            frag_now->tc_frag_data += expn.X_add_number;
            demand_empty_rest_of_line();
            return;
        }
        expn.X_add_number -= spare_bits;
        if (!bes && label) {
            symbol_set_frag(label, frag_now);
            S_SET_VALUE(label, frag_now_fix() - 1);
            label = NULL;
        }
    }

    words = (expn.X_add_number + bits_per_byte - 1) / bits_per_byte;
    bit_offset = expn.X_add_number % bits_per_byte;
    octets = words * OCTETS_PER_BYTE;

    if (octets < 0) {
        as_warn(_(".space/.bes repeat count is negative, ignored"));
        demand_empty_rest_of_line();
        return;
    }
    if (octets == 0) {
        as_warn(_(".space/.bes repeat count is zero, ignored"));
        demand_empty_rest_of_line();
        return;
    }

    if (now_seg == absolute_section) {
        abs_section_offset += words;
        if (bes && label)
            S_SET_VALUE(label, abs_section_offset - 1);
        frag_now->tc_frag_data = bit_offset;
        demand_empty_rest_of_line();
        return;
    }

    if (!need_pass_2)
        p = frag_var(rs_fill, 1, 1, 0, NULL, octets, NULL);
    frag_now->tc_frag_data = bit_offset;

    if (bes && label) {
        symbol_set_frag(label, frag_now);
        S_SET_VALUE(label, frag_now_fix() - 1);
    }

    if (p)
        *p = 0;

    demand_empty_rest_of_line();
}

/* [symbol] .usect "section-name", size-in-words
		   [, [blocking-flag] [, alignment-flag]]

   Uninitialized section.
   Non-zero blocking means that if the section would cross a page (128-word)
   boundary, it will be page-aligned.
   Non-zero alignment aligns on a longword boundary.

   Has no effect on the current section.  */

static void tic54x_usect(int x ATTRIBUTE_UNUSED)
{
    char c;
    char *name = NULL;
    char *section_name = NULL;
    segT seg, current_seg;
    subsegT current_subseg;
    int size = 0, blocking_flag = 0, alignment_flag = 0;
    flagword flags;
    char *p;

    ILLEGAL_WITHIN_STRUCT();

    current_seg = now_seg;
    current_subseg = now_subseg;

    c = get_symbol_name(&section_name);
    if (!section_name) {
        as_bad(_("Missing section name"));
        ignore_rest_of_line();
        return;
    }

    name = xstrdup(section_name);
    c = restore_line_pointer(c);

    if (*input_line_pointer == ',') {
        ++input_line_pointer;
    } else {
        as_bad(_("Missing size argument"));
        ignore_rest_of_line();
        free(name);
        return;
    }

    size = get_absolute_expression();

    if (*input_line_pointer == ',') {
        ++input_line_pointer;
        if (*input_line_pointer != ',') {
            blocking_flag = get_absolute_expression();
        } else {
            blocking_flag = 0;
        }
        if (*input_line_pointer == ',') {
            ++input_line_pointer;
            alignment_flag = get_absolute_expression();
        } else {
            alignment_flag = 0;
        }
    } else {
        blocking_flag = 0;
        alignment_flag = 0;
    }

    seg = subseg_new(name, 0);
    flags = bfd_section_flags(seg) | SEC_ALLOC;

    if (alignment_flag) {
        s_align_bytes(4);
        --input_line_pointer;
    }

    if (line_label != NULL) {
        S_SET_SEGMENT(line_label, seg);
        symbol_set_frag(line_label, frag_now);
        S_SET_VALUE(line_label, frag_now_fix());
        if (S_GET_STORAGE_CLASS(line_label) != C_EXT)
            S_SET_STORAGE_CLASS(line_label, C_LABEL);
    }

    seg_info(seg)->bss = 1;

    p = frag_var(rs_fill, 1, 1, 0, line_label, size * OCTETS_PER_BYTE, NULL);
    if (p)
        *p = 0;

    if (blocking_flag)
        flags |= SEC_TIC54X_BLOCK;

    if (!bfd_set_section_flags(seg, flags)) {
        as_warn(_("Error setting flags for \"%s\": %s"), name, bfd_errmsg(bfd_get_error()));
    }

    subseg_set(current_seg, current_subseg);

    demand_empty_rest_of_line();

    free(name);
}

static enum cpu_version lookup_version(const char *ver)
{
    if (!ver)
        return VNONE;

    size_t len = strlen(ver);
    if (len == 3 && ver[0] == '5' && ver[1] == '4' &&
        (ver[2] == '1' || ver[2] == '2' || ver[2] == '3' ||
         ver[2] == '5' || ver[2] == '8' || ver[2] == '9')) {
        return (enum cpu_version)(ver[2] - '0');
    }

    if (len == 5 && ver[0] == '5' && ver[1] == '4' &&
        (ver[2] == '5' || ver[2] == '6') &&
        (ver[3] == 'L' || ver[3] == 'l') &&
        (ver[4] == 'P' || ver[4] == 'p')) {
        return (enum cpu_version)(ver[2] - '0' + 10);
    }

    return VNONE;
}

static void set_cpu(enum cpu_version version)
{
    cpu = version;
    if (version == V545LP || version == V546LP) {
        symbolS *symbolP = symbol_new("__allow_lp", absolute_section, &zero_address_frag, 1);
        if (symbolP != NULL) {
            SF_SET_LOCAL(symbolP);
            symbol_table_insert(symbolP);
        }
    }
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

static void tic54x_version(int x ATTRIBUTE_UNUSED) {
    enum cpu_version version;
    enum cpu_version old_version = cpu;
    int c;
    char *ver;

    ILLEGAL_WITHIN_STRUCT();

    SKIP_WHITESPACE();
    ver = input_line_pointer;
    while (!is_end_of_stmt(*input_line_pointer)) {
        ++input_line_pointer;
    }
    c = *input_line_pointer;
    *input_line_pointer = '\0';

    version = lookup_version(ver);

    if ((cpu != VNONE && cpu != version) || version == VNONE) {
        if (cpu != VNONE && cpu != version) {
            as_warn(_("CPU version has already been set"));
        }
        if (version == VNONE) {
            as_bad(_("Unrecognized version '%s'"), ver);
        }
        ignore_rest_of_line();
        *input_line_pointer = c;
        return;
    }

    if (assembly_begun && version != old_version) {
        as_bad(_("Changing of CPU version on the fly not supported"));
        ignore_rest_of_line();
        *input_line_pointer = c;
        return;
    }

    set_cpu(version);

    *input_line_pointer = c;
    demand_empty_rest_of_line();
}

/* 'f' = float, 'x' = xfloat, 'd' = double, 'l' = ldouble.  */

static void tic54x_float_cons(int type) {
    if (current_stag != 0) {
        tic54x_struct_field('f');
    }

#ifdef md_flush_pending_output
    md_flush_pending_output();
#endif

    if (type != 'x') {
        frag_align(2, 0, 2);
        if (line_label) {
            symbol_set_frag(line_label, frag_now);
            S_SET_VALUE(line_label, frag_now_fix());
        }
    }

    float_cons('f');
}

/* The argument is capitalized if it should be zero-terminated
   's' is normal string with upper 8-bits zero-filled, 'p' is packed.
   Code copied from stringer, and slightly modified so that strings are packed
   and encoded into the correct octets.  */

static void tic54x_stringer(int type)
{
    unsigned int c = ',';
    int append_zero = (type == 'S' || type == 'P');
    int packed = (type == 'p' || type == 'P');
    int last_char = -1;

    if (current_stag != NULL)
    {
        tic54x_struct_field('*');
        return;
    }

#ifdef md_flush_pending_output
    md_flush_pending_output();
#endif

    while (c == ',')
    {
        SKIP_WHITESPACE();
        if (*input_line_pointer == '\"')
        {
            ++input_line_pointer;
            while (is_a_char((c = next_char_of_string())))
            {
                if (!packed)
                {
                    FRAG_APPEND_1_CHAR(c);
                    FRAG_APPEND_1_CHAR(0);
                }
                else
                {
                    if (last_char == -1)
                    {
                        last_char = c;
                    }
                    else
                    {
                        FRAG_APPEND_1_CHAR(c);
                        FRAG_APPEND_1_CHAR(last_char);
                        last_char = -1;
                    }
                }
            }
            if (append_zero)
            {
                if (packed && last_char != -1)
                {
                    FRAG_APPEND_1_CHAR(0);
                    FRAG_APPEND_1_CHAR(last_char);
                    last_char = -1;
                }
                else
                {
                    FRAG_APPEND_1_CHAR(0);
                    FRAG_APPEND_1_CHAR(0);
                }
            }
            if (input_line_pointer <= input_line_pointer - 1 || input_line_pointer[-1] != '\"')
            {
                /* Error: unterminated string literal */
                return;
            }
        }
        else
        {
            unsigned short value = get_absolute_expression();
            FRAG_APPEND_1_CHAR(value & 0xFF);
            FRAG_APPEND_1_CHAR((value >> 8) & 0xFF);
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

static void tic54x_p2align(int arg)
{
    (void)arg;
    as_bad(_("p2align not supported on this target"));
}

static void tic54x_align_words(int arg)
{
    int count = arg;

    if (!is_end_of_stmt(*input_line_pointer)) {
        if (arg == 2) {
            as_warn(_("Argument to .even ignored"));
        } else {
            count = get_absolute_expression();
        }
    }

    if (current_stag != NULL && arg == 128) {
        if (current_stag->current_bitfield_offset != 0) {
            current_stag->current_bitfield_offset = 0;
            abs_section_offset++;
        }
        demand_empty_rest_of_line();
        return;
    }

    ILLEGAL_WITHIN_STRUCT();
    s_align_bytes(count << 1);
}

/* Initialize multiple-bit fields within a single word of memory.  */

static void tic54x_field(int ignore ATTRIBUTE_UNUSED)
{
    expressionS expn;
    int size = 16;
    char *p = NULL;
    valueT value;
    symbolS *label = line_label;

    if (current_stag != NULL) {
        tic54x_struct_field('.');
        return;
    }

    input_line_pointer = parse_expression(input_line_pointer, &expn);

    if (*input_line_pointer == ',') {
        ++input_line_pointer;
        size = get_absolute_expression();
        if (size < 1 || size > 32) {
            as_bad(_("Invalid field size, must be from 1 to 32"));
            ignore_rest_of_line();
            return;
        }
    }

    if (expn.X_op != O_constant) {
        if (size != 16) {
            as_bad(_("field size must be 16 when value is relocatable"));
            ignore_rest_of_line();
            return;
        }
        frag_now->tc_frag_data = 0;
        emit_expr(&expn, 2);
    } else {
        unsigned long fmask = (size == 32) ? 0xFFFFFFFFul : (1ul << size) - 1;
        value = expn.X_add_number;
        expn.X_add_number &= fmask;
        if (value != (valueT)expn.X_add_number)
            as_warn(_("field value truncated"));
        value = expn.X_add_number;
        while (size >= 16) {
            frag_now->tc_frag_data = 0;
            p = frag_more(2);
            md_number_to_chars(p, (value >> (size - 16)) & 0xFFFF, 2);
            size -= 16;
        }
        if (size > 0) {
            int bit_offset = frag_bit_offset(frag_now, now_seg);
            fragS *alloc_frag = bit_offset_frag(frag_now, now_seg);

            if (bit_offset == -1) {
                struct bit_info *bi = XNEW(struct bit_info);
                expressionS size_exp;
                size_exp.X_op = O_constant;
                size_exp.X_add_number = size;
                bi->seg = now_seg;
                bi->type = TYPE_FIELD;
                bi->value = value;
                p = frag_var(rs_machine_dependent, 4, 1, 0,
                             make_expr_symbol(&size_exp), 0, (char *)bi);
                demand_empty_rest_of_line();
                return;
            }

            if (bit_offset == 0 || bit_offset + size > 16) {
                p = frag_more(2);
                frag_now->tc_frag_data = 0;
                alloc_frag = frag_now;
            } else {
                p = (alloc_frag == frag_now)
                    ? frag_now->fr_literal + frag_now_fix_octets() - 2
                    : alloc_frag->fr_literal;
                if (label != NULL) {
                    symbol_set_frag(label, alloc_frag);
                    if (alloc_frag == frag_now)
                        S_SET_VALUE(label, frag_now_fix() - 1);
                    label = NULL;
                }
            }

            value <<= 16 - alloc_frag->tc_frag_data - size;

            if (alloc_frag->tc_frag_data)
                value |= ((uint16_t)p[1] << 8) | p[0];
            md_number_to_chars(p, value, 2);
            alloc_frag->tc_frag_data += size;
            if (alloc_frag->tc_frag_data == 16)
                alloc_frag->tc_frag_data = 0;
        }
    }
    demand_empty_rest_of_line();
}

/* Ideally, we want to check SEC_LOAD and SEC_HAS_CONTENTS, but those aren't
   available yet.  seg_info ()->bss is the next best thing.  */

static int tic54x_initialized_section(segT seg)
{
  segment_info_type *info = seg_info(seg);
  if (info == NULL)
    return 0;
  return info->bss == 0;
}

/* .clink ["section name"]

   Marks the section as conditionally linked (link only if contents are
   referenced elsewhere.
   Without a name, refers to the current initialized section.
   Name is required for uninitialized sections.  */

static void tic54x_clink(int ignored ATTRIBUTE_UNUSED)
{
    segT seg = now_seg;

    ILLEGAL_WITHIN_STRUCT();

    if (*input_line_pointer == '\"')
    {
        char *section_name = ++input_line_pointer;
        char *name;
        while (is_a_char(next_char_of_string()))
            ;

        if (input_line_pointer <= section_name || input_line_pointer[-1] != '\"')
        {
            as_bad(_("Malformed section name"));
            ignore_rest_of_line();
            return;
        }

        input_line_pointer[-1] = 0;
        name = xstrdup(section_name);

        seg = bfd_get_section_by_name(stdoutput, name);
        free(name);

        if (seg == NULL)
        {
            as_bad(_("Unrecognized section '%s'"), section_name);
            ignore_rest_of_line();
            return;
        }
    }
    else
    {
        if (!tic54x_initialized_section(seg))
        {
            as_bad(_("Current section is uninitialized, section name required for .clink"));
            ignore_rest_of_line();
            return;
        }
    }

    if (seg != NULL)
        seg->flags |= SEC_TIC54X_CLINK;

    demand_empty_rest_of_line();
}

/* Change the default include directory to be the current source file's
   directory.  */

static void tic54x_set_default_include(void)
{
    unsigned lineno;
    const char *curfile = as_where(&lineno);
    const char *tmp = strrchr(curfile, '/');

    if (tmp != NULL)
    {
        size_t len = (size_t)(tmp - curfile);
        if (len > include_dir_maxlen)
            include_dir_maxlen = len;
        include_dirs[0] = notes_memdup(curfile, len, len + 1);
        if (include_dirs[0] == NULL)
        {
            /* Handle memory allocation failure */
            include_dirs[0] = ".";
        }
    }
    else
    {
        include_dirs[0] = ".";
    }
}

/* .include "filename" | filename
   .copy    "filename" | filename

   FIXME 'include' file should be omitted from any output listing,
     'copy' should be included in any output listing
   FIXME -- prevent any included files from changing listing (compat only)
   FIXME -- need to include source file directory in search path; what's a
      good way to do this?

   Entering/exiting included/copied file clears all local labels.  */

static void tic54x_include(int ignored ATTRIBUTE_UNUSED)
{
    static const char newblock[] = " .newblock\n";
    char *filename = NULL;
    char *input = NULL;
    int len = 0;

    ILLEGAL_WITHIN_STRUCT();
    SKIP_WHITESPACE();

    if (*input_line_pointer == '"') {
        filename = demand_copy_C_string(&len);
        if (!filename) {
            as_fatal("Failed to allocate memory for filename");
            return;
        }
        demand_empty_rest_of_line();
    } else {
        char *start = input_line_pointer;
        while (!is_end_of_stmt(*input_line_pointer)) {
            ++input_line_pointer;
        }
        char old = *input_line_pointer;
        *input_line_pointer = '\0';
        filename = xstrdup(start);
        *input_line_pointer = old;
        if (!filename) {
            as_fatal("Failed to duplicate filename");
            return;
        }
        demand_empty_rest_of_line();
    }

    input = concat("\"", filename, "\"\n", newblock, (char *)NULL);
    if (!input) {
        as_fatal("Failed to allocate memory for input string");
        free(filename);
        return;
    }
    input_scrub_insert_line(input);

    tic54x_clear_local_labels(0);
    tic54x_set_default_include();
    s_include(0);

    free(input);
    free(filename);
}

static void tic54x_message(int type)
{
    char *msg = NULL;
    char c;
    int len = 0;

    ILLEGAL_WITHIN_STRUCT();

    if (*input_line_pointer == '"') {
        msg = demand_copy_C_string(&len);
        if (msg == NULL) {
            as_bad("Failed to allocate memory for message string");
            demand_empty_rest_of_line();
            return;
        }
    } else {
        char *start = input_line_pointer;
        while (!is_end_of_stmt(*input_line_pointer)) {
            ++input_line_pointer;
        }
        c = *input_line_pointer;
        *input_line_pointer = '\0';
        msg = xstrdup(start);
        *input_line_pointer = c;

        if (msg == NULL) {
            as_bad("Failed to allocate memory for message string");
            demand_empty_rest_of_line();
            return;
        }
    }

    switch (type) {
        case 'm':
            as_tsktsk("%s", msg);
            break;
        case 'w':
            as_warn("%s", msg);
            break;
        case 'e':
            as_bad("%s", msg);
            break;
        default:
            as_bad("Unknown message type: %c", type);
            break;
    }

    demand_empty_rest_of_line();

    if (msg) {
        free(msg);
    }
}

/* .label <symbol>
   Define a special symbol that refers to the loadtime address rather than the
   runtime address within the current section.

   This symbol gets a special storage class so that when it is resolved, it is
   resolved relative to the load address (lma) of the section rather than the
   run address (vma).  */

static void tic54x_label(int ignored ATTRIBUTE_UNUSED)
{
    char *name = NULL;
    symbolS *symbolP = NULL;
    int c = 0;

    ILLEGAL_WITHIN_STRUCT();

    c = get_symbol_name(&name);
    if (!name) {
        as_fatal("Failed to get symbol name in tic54x_label");
        return;
    }
    symbolP = colon(name);
    if (!symbolP) {
        as_fatal("Failed to process label: %s", name);
        free(name);
        return;
    }
    S_SET_STORAGE_CLASS(symbolP, C_STATLAB);

    (void)restore_line_pointer(c);
    demand_empty_rest_of_line();

    free(name);
}

/* .mmregs
   Install all memory-mapped register names into the symbol table as
   absolute local symbols.  */

static void tic54x_register_mmregs(int ignored ATTRIBUTE_UNUSED)
{
    const tic54x_symbol *sym = tic54x_mmregs;

    ILLEGAL_WITHIN_STRUCT();

    while (sym->name) {
        symbolS *symbolP = symbol_new(sym->name, absolute_section, &zero_address_frag, sym->value);
        if (!symbolP) {
            continue;
        }
        SF_SET_LOCAL(symbolP);
        symbol_table_insert(symbolP);
        sym++;
    }
}

/* .loop [count]
   Count defaults to 1024.  */

static void tic54x_loop(int count) {
    ILLEGAL_WITHIN_STRUCT();

    SKIP_WHITESPACE();
    if (!is_end_of_stmt(*input_line_pointer)) {
        int expr = get_absolute_expression();
        if (expr < 0) {
            expr = 0;
        }
        count = expr;
    }

    do_repeat((size_t)count, "LOOP", "ENDLOOP", NULL);
}

/* Normally, endloop gets eaten by the preceding loop.  */

static void tic54x_endloop(int ignore)
{
    (void)ignore;
    as_bad(_("ENDLOOP without corresponding LOOP"));
    ignore_rest_of_line();
}

/* .break [condition].  */

static void tic54x_break(int ignore ATTRIBUTE_UNUSED)
{
    int cond = 1;

    ILLEGAL_WITHIN_STRUCT();

    SKIP_WHITESPACE();
    if (!is_end_of_stmt(*input_line_pointer)) {
        int expr = get_absolute_expression();
        if (expr < 0) {
            // Handle error from get_absolute_expression()
            return;
        }
        cond = expr;
    }

    if (cond) {
        end_repeat(substitution_line ? 1 : 0);
    }
}

static void set_address_mode(int mode) {
    amode = mode;
    if (mode != far_mode) {
        return;
    }

    symbolS *symbolP = symbol_new("__allow_far", absolute_section, &zero_address_frag, 1);
    if (!symbolP) {
        return;
    }
    SF_SET_LOCAL(symbolP);
    symbol_table_insert(symbolP);
}

static int address_mode_needs_set = 1;

static void tic54x_address_mode(int mode) {
    if (assembly_begun) {
        if (amode != (unsigned)mode) {
            as_bad(_("Mixing of normal and extended addressing not supported"));
            ignore_rest_of_line();
            return;
        }
    }
    if (mode == far_mode) {
        if (cpu != VNONE && cpu != V548 && cpu != V549) {
            as_bad(_("Extended addressing not supported on the specified CPU"));
            ignore_rest_of_line();
            return;
        }
    }
    set_address_mode(mode);
    demand_empty_rest_of_line();
}

/* .sblock "section"|section [,...,"section"|section]
   Designate initialized sections for blocking.  */

static void tic54x_sblock(int ignore ATTRIBUTE_UNUSED) {
    int c = ',';

    ILLEGAL_WITHIN_STRUCT();

    while (c == ',') {
        segT seg;
        char *name = NULL;
        int is_string = 0;

        if (*input_line_pointer == '"') {
            int len = 0;
            name = demand_copy_C_string(&len);
            is_string = 1;
            if (!name) {
                as_bad(_("Failed to parse string section name"));
                ignore_rest_of_line();
                return;
            }
        } else {
            char *section_name = NULL;
            c = get_symbol_name(&section_name);
            if (!section_name) {
                as_bad(_("Section name expected"));
                ignore_rest_of_line();
                return;
            }
            name = xstrdup(section_name);
            if (!name) {
                as_bad(_("Out of memory"));
                ignore_rest_of_line();
                return;
            }
            (void) restore_line_pointer(c);
        }

        seg = bfd_get_section_by_name(stdoutput, name);
        if (!seg) {
            as_bad(_("Unrecognized section '%s'"), name);
            ignore_rest_of_line();
            free(name);
            return;
        }
        if (!tic54x_initialized_section(seg)) {
            as_bad(_(".sblock may be used for initialized sections only"));
            ignore_rest_of_line();
            free(name);
            return;
        }

        seg->flags |= SEC_TIC54X_BLOCK;

        free(name);

        c = *input_line_pointer;
        if (!is_end_of_stmt(c))
            ++input_line_pointer;
    }

    demand_empty_rest_of_line();
}

/* symbol .set value
   symbol .equ value

   value must be defined externals; no forward-referencing allowed
   symbols assigned with .set/.equ may not be redefined.  */

static void tic54x_set(int ignore ATTRIBUTE_UNUSED)
{
    symbolS *symbolP = NULL;
    char *name = NULL;

    ILLEGAL_WITHIN_STRUCT();

    if (!line_label) {
        as_bad(_("Symbol missing for .set/.equ"));
        ignore_rest_of_line();
        return;
    }

    name = xstrdup(S_GET_NAME(line_label));
    line_label = NULL;

    symbolP = symbol_find(name);
    if (!symbolP)
        symbolP = md_undefined_symbol(name);
    if (!symbolP) {
        symbolP = symbol_new(name, absolute_section, &zero_address_frag, 0);
        if (!symbolP) {
            free(name);
            as_bad(_("Failed to create symbol for .set/.equ"));
            ignore_rest_of_line();
            return;
        }
        S_SET_STORAGE_CLASS(symbolP, C_STAT);
    }
    free(name);

    S_SET_DATA_TYPE(symbolP, T_INT);
    S_SET_SEGMENT(symbolP, absolute_section);
    symbol_table_insert(symbolP);
    pseudo_set(symbolP);
    demand_empty_rest_of_line();
}

/* .fclist
   .fcnolist
   List false conditional blocks.  */

static void tic54x_fclist(int show) {
    if (show) {
        listing &= ~LISTING_NOCOND;
    } else {
        listing |= LISTING_NOCOND;
    }

    if (!demand_empty_rest_of_line()) {
        // Handle error if demand_empty_rest_of_line fails
        // Depending on application: log, return, or abort
    }
}

static void tic54x_sslist(int show)
{
    if (ILLEGAL_WITHIN_STRUCT() != 0) {
        return;
    }
    listing_sslist = show;
}

/* .var SYM[,...,SYMN]
   Define a substitution string to be local to a macro.  */

static void tic54x_var(int ignore ATTRIBUTE_UNUSED) {
    char *name = NULL;
    int c;

    ILLEGAL_WITHIN_STRUCT();

    if (macro_level == 0) {
        as_bad(_(".var may only be used within a macro definition"));
        ignore_rest_of_line();
        return;
    }

    do {
        subsym_ent_t *ent = NULL;
        char *tmpname = NULL;

        if (!ISALPHA(*input_line_pointer)) {
            as_bad(_("Substitution symbols must begin with a letter"));
            ignore_rest_of_line();
            return;
        }

        c = get_symbol_name(&tmpname);

        if (!tmpname) {
            as_bad(_("Failed to get symbol name for .var"));
            ignore_rest_of_line();
            return;
        }

        name = xstrdup(tmpname);
        if (!name) {
            as_bad(_("Memory allocation failure for symbol name"));
            ignore_rest_of_line();
            return;
        }

        c = restore_line_pointer(c);

        ent = xmalloc(sizeof(*ent));
        if (!ent) {
            as_bad(_("Memory allocation failure for subsym_ent_t"));
            free(name);
            ignore_rest_of_line();
            return;
        }

        ent->u.s = (char *)"";
        ent->freekey = 1;
        ent->freeval = 0;
        ent->isproc = 0;
        ent->ismath = 0;

        if (!str_hash_insert(subsym_hash[macro_level], name, ent, 0)) {
            as_bad(_("Failed to insert symbol in hash"));
            free(name);
            free(ent);
            ignore_rest_of_line();
            return;
        }

        if (c == ',') {
            ++input_line_pointer;
            if (is_end_of_stmt(*input_line_pointer))
                c = *input_line_pointer;
        }

        free(name);
        name = NULL;
    } while (c == ',');

    demand_empty_rest_of_line();
}

/* .mlib <macro library filename>

   Macro libraries are archived (standard AR-format) text macro definitions
   Expand the file and include it.

   FIXME need to try the source file directory as well.  */

static void tic54x_mlib(int ignore ATTRIBUTE_UNUSED)
{
    char *filename = NULL;
    char *path = NULL;
    int len = 0;
    bfd *abfd = NULL, *mbfd = NULL;

    ILLEGAL_WITHIN_STRUCT();

    if (*input_line_pointer == '"')
    {
        filename = demand_copy_C_string(&len);
        if (filename == NULL)
            return;
    }
    else
    {
        SKIP_WHITESPACE();
        len = 0;
        while (!is_end_of_stmt(*input_line_pointer) && !is_whitespace(*input_line_pointer))
        {
            obstack_1grow(&notes, *input_line_pointer);
            ++input_line_pointer;
            ++len;
        }
        obstack_1grow(&notes, '\0');
        filename = obstack_finish(&notes);
    }
    demand_empty_rest_of_line();

    tic54x_set_default_include();
    path = notes_alloc(len + include_dir_maxlen + 2);
    if (path == NULL)
    {
        as_bad(_("out of memory allocating path buffer"));
        ignore_rest_of_line();
        return;
    }
    FILE *try = search_and_open(filename, path);
    if (try)
        fclose(try);

    register_dependency(path);

    abfd = bfd_openr(path, NULL);
    if (!abfd)
    {
        as_bad(_("can't open macro library file '%s' for reading: %s"),
               path, bfd_errmsg(bfd_get_error()));
        ignore_rest_of_line();
        return;
    }
    if (!bfd_check_format(abfd, bfd_archive))
    {
        as_bad(_("File '%s' not in macro archive format"), path);
        bfd_close(abfd);
        ignore_rest_of_line();
        return;
    }

    for (mbfd = bfd_openr_next_archived_file(abfd, NULL);
         mbfd != NULL;
         mbfd = bfd_openr_next_archived_file(abfd, mbfd))
    {
        bfd_size_type size = bfd_get_size(mbfd);
        if (size == 0)
        {
            as_warn(_("archive member is empty"));
            continue;
        }
        char *buf = XNEWVEC(char, size);
        if (buf == NULL)
        {
            as_bad(_("out of memory allocating buffer for archive member"));
            continue;
        }

        size = bfd_read(buf, size, mbfd);

        char fname[L_tmpnam];
        if (tmpnam(fname) == NULL)
        {
            as_bad(_("could not create temporary filename"));
            free(buf);
            continue;
        }

        FILE *ftmp = fopen(fname, "w+b");
        if (ftmp == NULL)
        {
            as_bad(_("could not open temporary file '%s' for writing"), fname);
            free(buf);
            continue;
        }

        if (size > 0)
        {
            if (fwrite(buf, 1, size, ftmp) != size)
            {
                as_bad(_("could not write to temporary file '%s'"), fname);
                fclose(ftmp);
                free(buf);
                remove(fname);
                continue;
            }
            if (buf[size-1] != '\n')
            {
                if (fwrite("\n", 1, 1, ftmp) != 1)
                {
                    as_bad(_("could not write newline to temporary file '%s'"), fname);
                    fclose(ftmp);
                    free(buf);
                    remove(fname);
                    continue;
                }
            }
        }
        fclose(ftmp);
        free(buf);

        input_scrub_insert_file(fname);
        remove(fname);
    }
    bfd_close(abfd);
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

int md_parse_option(int c, const char *arg)
{
    int version;
    FILE *fp;
    const char *filename;

    switch (c) {
    case OPTION_COFF_VERSION:
        version = atoi(arg);
        if (version < 0 || version > 2)
            as_fatal(_("Bad COFF version '%s'"), arg);
        break;

    case OPTION_CPU_VERSION:
        cpu = lookup_version(arg);
        if (cpu == VNONE)
            as_fatal(_("Bad CPU version '%s'"), arg);
        cpu_needs_set = 1;
        break;

    case OPTION_ADDRESS_MODE:
        amode = far_mode;
        address_mode_needs_set = 1;
        break;

    case OPTION_STDERR_TO_FILE:
        filename = arg;
        fp = fopen(filename, "w+");
        if (!fp)
            as_fatal(_("Can't redirect stderr to the file '%s'"), filename);
        fclose(fp);
        fp = freopen(filename, "w+", stderr);
        if (!fp)
            as_fatal(_("Can't redirect stderr to the file '%s'"), filename);
        break;

    default:
        return 0;
    }

    return 1;
}

/* Create a "local" substitution string hash table for a new macro level
   Some docs imply that macros have to use .newblock in order to be able
   to re-use a local label.  We effectively do an automatic .newblock by
   deleting the local label hash between macro invocations.  */

void tic54x_macro_start(void) {
    if (macro_level + 1 >= MAX_SUBSYM_HASH) {
        as_fatal(_("Macro nesting is too deep"));
        return;
    }

    macro_level++;
    subsym_hash[macro_level] = subsym_htab_create();
    if (!subsym_hash[macro_level]) {
        as_fatal(_("Failed to create subsym hash table"));
        macro_level--;
        return;
    }

    local_label_hash[macro_level] = local_label_htab_create();
    if (!local_label_hash[macro_level]) {
        as_fatal(_("Failed to create local label hash table"));
        subsym_htab_destroy(subsym_hash[macro_level]);
        subsym_hash[macro_level] = NULL;
        macro_level--;
        return;
    }
}

void tic54x_macro_info(const macro_entry *macro) {
    if (!macro || !macro->formals) {
        return;
    }

    const formal_entry *entry = macro->formals;
    while (entry) {
        char *name = xstrndup(entry->name.ptr, entry->name.len);
        if (!name) {
            // Handle allocation failure
            break;
        }

        subsym_ent_t *ent = xmalloc(sizeof(*ent));
        if (!ent) {
            free(name);
            // Handle allocation failure
            break;
        }

        ent->u.s = xstrndup(entry->actual.ptr, entry->actual.len);
        if (!ent->u.s) {
            free(ent);
            free(name);
            // Handle allocation failure
            break;
        }

        ent->freekey = 1;
        ent->freeval = 1;
        ent->isproc = 0;
        ent->ismath = 0;

        str_hash_insert(subsym_hash[macro_level], name, ent, 0);

        entry = entry->next;
    }
}

/* Get rid of this macro's .var's, arguments, and local labels.  */

void tic54x_macro_end(void)
{
    if (macro_level < 0)
        return;

    if (subsym_hash[macro_level]) {
        htab_delete(subsym_hash[macro_level]);
        subsym_hash[macro_level] = NULL;
    }

    if (local_label_hash[macro_level]) {
        htab_delete(local_label_hash[macro_level]);
        local_label_hash[macro_level] = NULL;
    }

    macro_level--;
}

static int subsym_symlen(char *a, char *ignore)
{
    if (a == NULL) {
        return 0;
    }
    (void)ignore;
    return (int)strlen(a);
}

/* Compare symbol A to string B.  */

static int subsym_symcmp(const char *a, const char *b) {
    if (a == NULL || b == NULL) {
        return (a == b) ? 0 : (a == NULL ? -1 : 1);
    }
    return strcmp(a, b);
}

/* Return the index of the first occurrence of B in A, or zero if none
   assumes b is an integer char value as a string.  Index is one-based.  */

static int subsym_firstch(const char *a, const char *b)
{
    if (!a || !b) {
        return 0;
    }

    char *endptr;
    long val = strtol(b, &endptr, 10);
    if (endptr == b || val < 0 || val > 255) {
        return 0;
    }

    char ch = (char)val;
    const char *tmp = strchr(a, ch);

    return tmp ? (int)(tmp - a) + 1 : 0;
}

/* Similar to firstch, but returns index of last occurrence of B in A.  */

static int subsym_lastch(const char *a, const char *b)
{
    if (!a || !b) {
        return 0;
    }

    char ch;
    int ival = atoi(b);
    if (ival < 0 || ival > 255) {
        return 0;
    }
    ch = (char)ival;

    const char *tmp = strrchr(a, ch);
    if (!tmp) {
        return 0;
    }
    return (int)(tmp - a + 1);
}

/* Returns 1 if string A is defined in the symbol table (NOT the substitution
   symbol table).  */

static int subsym_isdefed(const char *a, const char *ignore ATTRIBUTE_UNUSED) {
    return symbol_find(a) != NULL;
}

/* Assign first member of comma-separated list B (e.g. "1,2,3") to the symbol
   A, or zero if B is a null string.  Both arguments *must* be substitution
   symbols, unsubstituted.  */

static int subsym_ismember(char *sym, char *list) {
    if (!list) {
        return 0;
    }

    subsym_ent_t *listv = subsym_lookup(list, macro_level);
    if (!listv) {
        as_bad(_("Undefined substitution symbol '%s'"), list);
        ignore_rest_of_line();
        return 0;
    }

    if (listv->isproc) {
        as_bad(_("Substitution symbol '%s' is a procedure"), list);
        ignore_rest_of_line();
        return 0;
    }

    char *dup_list = notes_strdup(listv->u.s);
    if (!dup_list) {
        as_bad(_("Memory allocation failed for substitution symbol '%s'"), list);
        ignore_rest_of_line();
        return 0;
    }

    char *comma = strchr(dup_list, ',');
    if (comma)
        *comma = '\0';

    subsym_create_or_replace(sym, dup_list);

    if (comma) {
        subsym_create_or_replace(list, comma + 1);
        free(dup_list);
        return *(comma + 1) != '\0';
    } else {
        subsym_create_or_replace(list, "");
        free(dup_list);
        return 0;
    }
}

/* Return zero if not a constant; otherwise:
   1 if binary
   2 if octal
   3 if hexadecimal
   4 if character
   5 if decimal.  */

static int subsym_iscons(char *a, char *ignore ATTRIBUTE_UNUSED)
{
    expressionS expn;
    size_t len;

    if (!a)
        return 0;

    parse_expression(a, &expn);

    if (expn.X_op != O_constant)
        return 0;

    len = strlen(a);
    if (len == 0)
        return 0;

    switch (TOUPPER(a[len - 1])) {
        case 'B': return 1;
        case 'Q': return 2;
        case 'H': return 3;
        case '\'': return 4;
        default: break;
    }

    if (*a == '0' && len > 1) {
        if (TOUPPER(a[1]) == 'X')
            return 3;
        return 2;
    }

    return 5;
}

/* Return 1 if A is a valid symbol name.  Expects string input.   */

static int subsym_isname(const char *a, const char *ignore ATTRIBUTE_UNUSED)
{
    if (a == NULL || !is_name_beginner(*a))
        return 0;
    for (; *a; ++a) {
        if (!is_part_of_name(*a))
            return 0;
    }
    return 1;
}

/* Return whether the string is a register; accepts ar0-7, unless .mmregs has
   been seen; if so, recognize any memory-mapped register.
   Note this does not recognize "A" or "B" accumulators.  */

static int subsym_isreg(const char *a, const char *ignore ATTRIBUTE_UNUSED)
{
    return str_hash_find(reg_hash, a) != NULL || str_hash_find(mmreg_hash, a) != NULL;
}

/* Return the structure size, given the stag.  */

static int subsym_structsz(const char *name, const char *ignore)
{
    if (name == NULL) {
        return 0;
    }

    struct stag *stag = str_hash_find(stag_hash, name);
    return stag ? stag->size : 0;
}

/* If anybody actually uses this, they can fix it :)
   FIXME I'm not sure what the "reference point" of a structure is.  It might
   be either the initial offset given .struct, or it may be the offset of the
   structure within another structure, or it might be something else
   altogether.  since the TI assembler doesn't seem to ever do anything but
   return zero, we punt and return zero.  */

static int subsym_structacc(void) {
  return 0;
}

static float math_ceil(float arg1, float ignore)
{
    (void)ignore;
    return (float)ceilf(arg1);
}

static int math_cvi(float arg1, float ignore)
{
    (void)ignore;
    return (int)arg1;
}

static float math_floor(float arg1, float ignore)
{
    (void)ignore;
    return floorf(arg1);
}

#include <math.h>
#include <errno.h>
#include <float.h>

static float math_fmod(float arg1, float arg2)
{
    if (arg2 == 0.0f) {
        errno = EDOM;
        return NAN;
    }
    return fmodf(arg1, arg2);
}

static int math_int(float arg1, float ignore)
{
    (void)ignore;
    int int_val = (int)arg1;
    return (arg1 == (float)int_val) ? 1 : 0;
}

static float math_round(float value, float unused)
{
    (void)unused;
    if (value > 0.0f)
        return (float)((int)(value + 0.5f));
    else
        return (float)((int)(value - 0.5f));
}

static int math_sgn(float arg1, float ignore ATTRIBUTE_UNUSED)
{
    if (arg1 < 0.0f)
        return -1;
    if (arg1 > 0.0f)
        return 1;
    return 0;
}

static float math_trunc(float arg1, float ignore)
{
    (void)ignore;
    return (float)((int)arg1);
}

static float math_acos(float arg1, float ignore)
{
    (void)ignore;
    return (float)acosf(arg1);
}

#include <math.h>
#include <errno.h>
#include <float.h>

static float math_asin(float arg1, float ignore)
{
    (void)ignore;
    if (arg1 < -1.0f || arg1 > 1.0f) {
        errno = EDOM;
        return NAN;
    }
    return asinf(arg1);
}

static float math_atan(float arg1, float unused)
{
    (void)unused;
    return (float)atanf(arg1);
}

#include <math.h>
#include <errno.h>
#include <float.h>

static float math_atan2(float y, float x)
{
    if (!isfinite(y) || !isfinite(x)) {
        errno = EDOM;
        return NAN;
    }
    if (x == 0.0f && y == 0.0f) {
        errno = EDOM;
        return NAN;
    }
    float result = (float)atan2((double)y, (double)x);
    if (!isfinite(result)) {
        errno = ERANGE;
        return NAN;
    }
    return result;
}

static float math_cosh(float arg1)
{
    return (float)cosh(arg1);
}

static float math_cos(float arg1, float ignore) {
    (void)ignore;
    return cosf(arg1);
}

static float math_cvf(float arg1, float ignore)
{
  (void)ignore;
  return arg1;
}

static float math_exp(float arg1, float ignore)
{
    (void)ignore;
    return (float)expf(arg1);
}

static float math_fabs(float arg1)
{
    return fabsf(arg1);
}

/* expr1 * 2^expr2.  */

#include <math.h>
#include <errno.h>
#include <float.h>

static float math_ldexp(float arg1, float arg2) {
    if (!isfinite(arg1) || !isfinite(arg2)) {
        errno = EDOM;
        return NAN;
    }
    double result = arg1 * pow(2.0, arg2);
    if (result > FLT_MAX) {
        errno = ERANGE;
        return HUGE_VALF;
    }
    if (result < -FLT_MAX) {
        errno = ERANGE;
        return -HUGE_VALF;
    }
    if (result == 0.0 && arg1 != 0.0) {
        errno = ERANGE;
    }
    return (float)result;
}

#include <math.h>

static float math_log10(float arg1)
{
    if (arg1 <= 0.0f) {
        return NAN;
    }
    return log10f(arg1);
}


static float math_log(float arg1, float ignore)
{
    (void)ignore;
    return logf(arg1);
}

static float math_max(float arg1, float arg2)
{
    return fmaxf(arg1, arg2);
}

static float math_min(float arg1, float arg2)
{
    return fminf(arg1, arg2);
}

#include <math.h>

float math_pow(float base, float exponent) {
    if (isnan(base) || isnan(exponent)) {
        return NAN;
    }
    return powf(base, exponent);
}

static float math_sin(float arg1, float ignore)
{
    (void)ignore;
    return sinf(arg1);
}

static float math_sinh(float arg1)
{
    return (float)sinhf(arg1);
}

static float math_sqrt(float arg1, float ignore)
{
    if (arg1 < 0.0f) {
        return 0.0f;
    }
    return sqrtf(arg1);
}

static float math_tan(float arg1)
{
    return (float)tan(arg1);
}

static float math_tanh(float arg1, float ignore)
{
    (void)ignore;
    return (float)tanhf(arg1);
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
    insn_template *tm;
    const tic54x_symbol *sym;
    const subsym_proc_entry *subsym_proc;
    const char **symname;
    char *env_tic54x_dir = getenv("TIC54X_DIR");
    char *env_a_dir = getenv("A_DIR");
    const char *A_DIR = env_tic54x_dir ? env_tic54x_dir : env_a_dir;

    local_label_id = 0;

    if (A_DIR && *A_DIR)
    {
        char *dirs = notes_strdup(A_DIR);
        char *p = dirs;
        char *next;

        while (p && *p)
        {
            next = strchr(p, ';');
            if (next)
            {
                *next = '\0';
                next++;
            }
            add_include_dir(p);
            p = next;
        }
        free(dirs);
    }

    op_hash = str_htab_create();
    for (tm = (insn_template *)tic54x_optab; tm->name; ++tm)
        str_hash_insert(op_hash, tm->name, tm, 0);

    parop_hash = str_htab_create();
    for (tm = (insn_template *)tic54x_paroptab; tm->name; ++tm)
        str_hash_insert(parop_hash, tm->name, tm, 0);

    reg_hash = str_htab_create();
    for (sym = tic54x_regs; sym->name; ++sym)
    {
        symbolS *symbolP = symbol_new(sym->name, absolute_section, &zero_address_frag, sym->value);
        SF_SET_LOCAL(symbolP);
        symbol_table_insert(symbolP);
        str_hash_insert(reg_hash, sym->name, sym, 0);
    }
    for (sym = tic54x_mmregs; sym->name; ++sym)
        str_hash_insert(reg_hash, sym->name, sym, 0);

    mmreg_hash = str_htab_create();
    for (sym = tic54x_mmregs; sym->name; ++sym)
        str_hash_insert(mmreg_hash, sym->name, sym, 0);

    cc_hash = str_htab_create();
    for (sym = tic54x_condition_codes; sym->name; ++sym)
        str_hash_insert(cc_hash, sym->name, sym, 0);

    cc2_hash = str_htab_create();
    for (sym = tic54x_cc2_codes; sym->name; ++sym)
        str_hash_insert(cc2_hash, sym->name, sym, 0);

    cc3_hash = str_htab_create();
    for (sym = tic54x_cc3_codes; sym->name; ++sym)
        str_hash_insert(cc3_hash, sym->name, sym, 0);

    sbit_hash = str_htab_create();
    for (sym = tic54x_status_bits; sym->name; ++sym)
        str_hash_insert(sbit_hash, sym->name, sym, 0);

    misc_symbol_hash = str_htab_create();
    for (symname = tic54x_misc_symbols; *symname; ++symname)
        str_hash_insert(misc_symbol_hash, *symname, *symname, 0);

    local_label_hash[0] = local_label_htab_create();
    subsym_hash[0] = subsym_htab_create();
    for (subsym_proc = subsym_procs; subsym_proc->name; ++subsym_proc)
    {
        subsym_ent_t *ent = (subsym_ent_t *)xmalloc(sizeof(*ent));
        ent->u.p = subsym_proc;
        ent->freekey = 0;
        ent->freeval = 0;
        ent->isproc = 1;
        ent->ismath = subsym_proc->type != 0;
        str_hash_insert(subsym_hash[0], subsym_proc->name, ent, 0);
    }
    subsym_recurse_hash = str_htab_create();
    stag_hash = str_htab_create();
}

void tic54x_md_end(void)
{
    htab_delete(stag_hash);
    htab_delete(subsym_recurse_hash);

    while (macro_level > -1) {
        tic54x_macro_end();
        macro_level--;
    }
    macro_level = 0;

    htab_delete(misc_symbol_hash);
    htab_delete(sbit_hash);
    htab_delete(cc3_hash);
    htab_delete(cc2_hash);
    htab_delete(cc_hash);
    htab_delete(mmreg_hash);
    htab_delete(reg_hash);
    htab_delete(parop_hash);
    htab_delete(op_hash);
}

static int is_accumulator(const struct opstruct *operand)
{
    if (!operand || !operand->buf) {
        return 0;
    }
    return strcasecmp(operand->buf, "a") == 0 || strcasecmp(operand->buf, "b") == 0;
}

/* Return the number of operands found, or -1 on error, copying the
   operands into the given array and the accompanying expressions into
   the next array.  */

static int get_operands(struct opstruct operands[], char *line) {
    char *lptr = line;
    int numexp = 0;
    int i;

    while (numexp < MAX_OPERANDS && !is_end_of_stmt(*lptr)) {
        int paren_balance = 0;
        char *op_start, *op_end;

        while (is_whitespace(*lptr)) ++lptr;
        op_start = lptr;

        while (1) {
            if (*lptr == '\0' || (!paren_balance && *lptr == ',')) break;
            if (*lptr == '(') ++paren_balance;
            else if (*lptr == ')') --paren_balance;
            ++lptr;
        }

        op_end = lptr;
        if (op_end != op_start) {
            int len = op_end - op_start;
            if (len >= sizeof(operands[numexp].buf)) len = sizeof(operands[numexp].buf) - 1;
            memcpy(operands[numexp].buf, op_start, len);
            operands[numexp].buf[len] = 0;
            while (len > 0 && is_whitespace(operands[numexp].buf[len - 1]))
                operands[numexp].buf[--len] = 0;
            ++numexp;
        } else if (*lptr == ',') {
            as_bad(_("Expecting operand after ','"));
            return -1;
        }

        if (*lptr == ',') {
            ++lptr;
            if (*lptr == '\0') {
                as_bad(_("Expecting operand after ','"));
                return -1;
            }
        }
    }

    while (is_whitespace(*lptr)) ++lptr;
    if (!is_end_of_stmt(*lptr)) {
        as_bad(_("Extra junk on line"));
        return -1;
    }

    for (i = 0; i < numexp; i++) {
        memset(&operands[i].exp, 0, sizeof(operands[i].exp));
        char *buf = operands[i].buf;
        if (buf[0] == '#' || buf[0] == '@') {
            parse_expression(buf + 1, &operands[i].exp);
        } else if (buf[0] == '*') {
            char *paren = strchr(buf, '(');
            if (paren && paren[1] == '#') ++paren;
            if (paren) {
                char *end = strrchr(paren, ')');
                if (!end) {
                    as_bad(_("Badly formed address expression"));
                    return -1;
                }
                char temp = *(end + 1);
                *(end + 1) = '\0';
                parse_expression(paren, &operands[i].exp);
                *(end + 1) = temp;
            } else {
                operands[i].exp.X_op = O_absent;
            }
        } else {
            parse_expression(buf, &operands[i].exp);
        }
    }

    return numexp;
}

/* Predicates for different operand types.  */

static int is_immediate(const struct opstruct *operand) {
    if (operand == NULL || operand->buf == NULL) {
        return 0;
    }
    return operand->buf[0] == '#';
}

/* This is distinguished from immediate because some numbers must be constants
   and must *not* have the '#' prefix.  */

static int is_absolute(const struct opstruct *operand) {
    if (operand == NULL) {
        return 0;
    }
    return operand->exp.X_op == O_constant && !is_immediate(operand);
}

/* Is this an indirect operand?  */

static int is_indirect(const struct opstruct *operand) {
    if (!operand || !operand->buf)
        return 0;
    return operand->buf[0] == '*';
}

/* Is this a valid dual-memory operand?  */

static int is_dual(struct opstruct *operand) {
    if (!is_indirect(operand) || strncasecmp(operand->buf, "*ar", 3) != 0) {
        return 0;
    }

    const char *tmp = operand->buf + 3;
    if (*tmp < '0' || *tmp > '9') {
        return 0;
    }

    int arf = *tmp - '0';
    tmp++;

    if (arf < 2 || arf > 5) {
        return 0;
    }

    if (*tmp == '\0') {
        return 1;
    }
    if (strcmp(tmp, "-") == 0) {
        return 1;
    }
    if (strcmp(tmp, "+") == 0) {
        return 1;
    }
    if (strcasecmp(tmp, "+0%") == 0) {
        return 1;
    }

    return 0;
}

static int is_mmreg(struct opstruct *operand)
{
    if (!operand) {
        return 0;
    }
    if (is_absolute(operand) || is_immediate(operand)) {
        return 1;
    }
    return str_hash_find(mmreg_hash, operand->buf) != NULL;
}

static int is_type(struct opstruct *operand, enum optype type)
{
    if (!operand) return 0;

    switch (type) {
        case OP_None:
            return operand->buf[0] == 0;
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
        case OP_B: {
            int r = is_accumulator(operand);
            if (!r) return 0;
            return TOUPPER(operand->buf[0]) == 'B';
        }
        case OP_A: {
            int r = is_accumulator(operand);
            if (!r) return 0;
            return TOUPPER(operand->buf[0]) == 'A';
        }
        case OP_ARX:
            return strncasecmp("ar", operand->buf, 2) == 0 && ISDIGIT(operand->buf[2]);
        case OP_SBIT:
            return (str_hash_find(sbit_hash, operand->buf) != 0) || is_absolute(operand);
        case OP_CC:
            return str_hash_find(cc_hash, operand->buf) != 0;
        case OP_CC2:
            return str_hash_find(cc2_hash, operand->buf) != 0;
        case OP_CC3:
            return (str_hash_find(cc3_hash, operand->buf) != 0) || is_immediate(operand) || is_absolute(operand);
        case OP_16:
            return (is_immediate(operand) || is_absolute(operand)) && operand->exp.X_add_number == 16;
        case OP_N:
            if (is_absolute(operand) || is_immediate(operand)) return 1;
            if (strcasecmp("st0", operand->buf) == 0 || strcasecmp("st1", operand->buf) == 0) return 1;
            return 0;
        case OP_12:
        case OP_123:
            return is_absolute(operand) || is_immediate(operand);
        case OP_SHFT:
            if (is_immediate(operand) || is_absolute(operand))
                return operand->exp.X_add_number >= 0 && operand->exp.X_add_number < 16;
            return 0;
        case OP_SHIFT:
            if (is_immediate(operand) || is_absolute(operand))
                return operand->exp.X_add_number != 16;
            return 0;
        case OP_BITC:
        case OP_031:
        case OP_k8:
            return is_absolute(operand) || is_immediate(operand);
        case OP_k8u:
            return is_immediate(operand)
                   && operand->exp.X_op == O_constant
                   && operand->exp.X_add_number >= 0
                   && operand->exp.X_add_number < 256;
        case OP_k5:
        case OP_k3:
        case OP_k9:
            return is_immediate(operand);
        case OP_T:
            return strcasecmp("t", operand->buf) == 0 || strcasecmp("treg", operand->buf) == 0;
        case OP_TS:
            return strcasecmp("ts", operand->buf) == 0;
        case OP_ASM:
            return strcasecmp("asm", operand->buf) == 0;
        case OP_TRN:
            return strcasecmp("trn", operand->buf) == 0;
        case OP_DP:
            return strcasecmp("dp", operand->buf) == 0;
        case OP_ARP:
            return strcasecmp("arp", operand->buf) == 0;
        default:
            return 0;
    }
}

static int operands_match(tic54x_insn *insn, struct opstruct *operands, int opcount, const enum optype *refoptype, int minops, int maxops) {
    int op = 0, refop = 0, totalops = maxops;

    if (opcount == 0 && minops == 0)
        return 1;

    while (op < opcount && refop <= totalops) {
        if (!is_type(&operands[op], OPTYPE(refoptype[refop]))) {
            if (refoptype[refop] & OPT) {
                refop++;
                continue;
            } else {
                return 0;
            }
        }
        operands[op].type = OPTYPE(refoptype[refop]);
        refop++;
        op++;
    }
    if (op < opcount)
        return 0;
    while (refop <= totalops) {
        if ((refoptype[refop] & OPT) == 0)
            return 0;
        if (OPTYPE(refoptype[refop]) == OP_DST)
            insn->using_default_dst = 1;
        refop++;
    }
    return 1;
}

/* 16-bit direct memory address
   Explicit dmad operands are always in last word of insn (usually second
   word, but bumped to third if lk addressing is used)

   We allow *(dmad) notation because the TI assembler allows it.

   XPC_CODE:
   0 for 16-bit addresses
   1 for full 23-bit addresses
   2 for the upper 7 bits of a 23-bit address (LDX).  */

static int encode_dmad(tic54x_insn *insn, struct opstruct *operand, int xpc_code)
{
    int op = 1 + insn->is_lkaddr;
    size_t buf_len;

    if (!operand || !operand->buf) {
        as_bad(_("Null operand in dmad encoding"));
        return 0;
    }

    buf_len = strlen(operand->buf);
    if (is_indirect(operand) && (buf_len == 0 || operand->buf[buf_len - 1] != ')')) {
        as_bad(_("Invalid dmad syntax '%s'"), operand->buf);
        return 0;
    }

    insn->opcode[op].addr_expr = operand->exp;

    if (insn->opcode[op].addr_expr.X_op == O_constant) {
        valueT value = insn->opcode[op].addr_expr.X_add_number;

        switch (xpc_code) {
        case 1:
            insn->opcode[0].word &= 0xFF80;
            insn->opcode[0].word |= (value >> 16) & 0x7F;
            insn->opcode[1].word = value & 0xFFFF;
            break;
        case 2:
            insn->opcode[op].word = (value >> 16) & 0xFFFF;
            break;
        default:
            insn->opcode[op].word = value;
            break;
        }
        return 1;
    }

    insn->opcode[op].word = 0;
    insn->opcode[op].r_nchars = 2;

    if (amode == c_mode) {
        insn->opcode[op].r_type = BFD_RELOC_TIC54X_16_OF_23;
    } else if (xpc_code == 1) {
        insn->opcode[0].addr_expr = operand->exp;
        insn->opcode[0].r_type = BFD_RELOC_TIC54X_23;
        insn->opcode[0].r_nchars = 4;
        insn->opcode[0].unresolved = 1;
        insn->words = 1;
        goto done;
    } else if (xpc_code == 2) {
        insn->opcode[op].r_type = BFD_RELOC_TIC54X_MS7_OF_23;
    } else {
        insn->opcode[op].r_type = BFD_RELOC_TIC54X_16_OF_23;
    }

    insn->opcode[op].unresolved = 1;
done:
    return 1;
}

/* 7-bit direct address encoding.  */

static int encode_address(tic54x_insn *insn, struct opstruct *operand)
{
    if (!insn || !operand)
        return 0;

    insn->opcode[0].addr_expr = operand->exp;

    switch (operand->exp.X_op) {
        case O_constant:
            insn->opcode[0].word |= (operand->exp.X_add_number & 0x7F);
            break;
        case O_register:
            as_bad(_("Use the .mmregs directive to use memory-mapped register names such as '%s'"), operand->buf);
            insn->opcode[0].r_nchars = 1;
            insn->opcode[0].r_type = BFD_RELOC_TIC54X_PARTLS7;
            insn->opcode[0].unresolved = 1;
            break;
        default:
            insn->opcode[0].r_nchars = 1;
            insn->opcode[0].r_type = BFD_RELOC_TIC54X_PARTLS7;
            insn->opcode[0].unresolved = 1;
            break;
    }

    return 1;
}

static int encode_indirect(tic54x_insn *insn, struct opstruct *operand)
{
    int arf = 0;
    int mod = 0;

    if (insn->is_lkaddr)
    {
        char c = operand->buf[1];
        if (TOUPPER(c) == 'A') {
            mod = 12;
            arf = operand->buf[3] - '0';
        } else if (c == '(') {
            mod = 15;
            arf = 0;
        } else if (strchr(operand->buf, '%') != NULL) {
            mod = 14;
            arf = operand->buf[4] - '0';
        } else {
            mod = 13;
            arf = operand->buf[4] - '0';
        }

        insn->opcode[1].addr_expr = operand->exp;

        if (operand->exp.X_op == O_constant) {
            insn->opcode[1].word = operand->exp.X_add_number;
        } else {
            insn->opcode[1].word = 0;
            insn->opcode[1].r_nchars = 2;
            insn->opcode[1].r_type = BFD_RELOC_TIC54X_16_OF_23;
            insn->opcode[1].unresolved = 1;
        }
    }
    else if (strncasecmp(operand->buf, "*sp (", 4) == 0)
    {
        return encode_address(insn, operand);
    }
    else
    {
        char *buf = operand->buf;
        int idx_arf;
        int len = strlen(buf);

        if (TOUPPER(buf[1]) == 'A')
            idx_arf = 3;
        else
            idx_arf = 4;

        arf = buf[idx_arf] - '0';

        if (buf[1] == '+')
        {
            mod = 3;
            if ((insn->tm->flags & FL_SMR) != 0)
                as_warn(_("Address mode *+ARx is write-only. Results of reading are undefined."));
        }
        else if (buf[4] == '\0')
        {
            mod = 0;
        }
        else if (buf[5] == '\0')
        {
            mod = (buf[4] == '-') ? 1 : 2;
        }
        else if (buf[6] == '\0')
        {
            if (buf[5] == '0')
                mod = (buf[4] == '-') ? 5 : 6;
            else
                mod = (buf[4] == '-') ? 8 : 10;
        }
        else if (TOUPPER(buf[6]) == 'B')
        {
            mod = (buf[4] == '-') ? 4 : 7;
        }
        else if (TOUPPER(buf[6]) == '%')
        {
            mod = (buf[4] == '-') ? 9 : 11;
        }
        else
        {
            as_bad(_("Unrecognized indirect address format \"%s\""), buf);
            return 0;
        }
    }

    insn->opcode[0].word |= (0x80 | (mod << 3) | arf);

    return 1;
}


static int encode_integer(tic54x_insn *insn, struct opstruct *operand, int which, int min, int max, unsigned short mask)
{
    long parse, integer;

    if (!insn || !operand)
        return 0;

    insn->opcode[which].addr_expr = operand->exp;

    if (operand->exp.X_op == O_constant)
    {
        parse = operand->exp.X_add_number;
        if ((parse & 0x8000) && min == -32768 && max == 32767)
            integer = (short)parse;
        else
            integer = parse;

        if (integer >= min && integer <= max)
        {
            insn->opcode[which].word |= (integer & mask);
            return 1;
        }
        as_bad(_("Operand '%s' out of range (%d <= x <= %d)"), operand->buf, min, max);
        return 0;
    }

    if (insn->opcode[which].addr_expr.X_op == O_constant)
    {
        insn->opcode[which].word |= insn->opcode[which].addr_expr.X_add_number & mask;
        return 1;
    }

    bfd_reloc_code_real_type rtype;
    int size;

    switch (mask)
    {
        case 0x1FF:
            rtype = BFD_RELOC_TIC54X_PARTMS9;
            size = 2;
            break;
        case 0xFFFF:
            rtype = BFD_RELOC_TIC54X_16_OF_23;
            size = 2;
            break;
        case 0x7F:
            rtype = BFD_RELOC_TIC54X_PARTLS7;
            size = 1;
            break;
        default:
            rtype = BFD_RELOC_8;
            size = 1;
            break;
    }

    if (rtype == BFD_RELOC_8)
    {
        as_bad(_("Error in relocation handling"));
        return 0;
    }

    insn->opcode[which].r_nchars = size;
    insn->opcode[which].r_type = rtype;
    insn->opcode[which].unresolved = 1;

    return 1;
}

static int encode_condition(tic54x_insn *insn, struct opstruct *operand) {
    tic54x_symbol *cc = str_hash_find(cc_hash, operand->buf);
    if (!cc) {
        as_bad(_("Unrecognized condition code \"%s\""), operand->buf);
        return 0;
    }

    #define CC_GROUP 0x40
    #define CC_ACC   0x08
    #define CATG_A1  0x07
    #define CATG_B1  0x30
    #define CATG_A2  0x30
    #define CATG_B2  0x0C
    #define CATG_C2  0x03

    unsigned word = insn->opcode[0].word;
    unsigned cc_val = cc->value;

    if ((word & 0xFF) != 0) {
        int word_group = word & CC_GROUP;
        int cc_group = cc_val & CC_GROUP;
        if (word_group != cc_group) {
            as_bad(_("Condition \"%s\" does not match preceding group"), operand->buf);
            return 0;
        }
        if (word_group) {
            if ((word & CC_ACC) != (cc_val & CC_ACC)) {
                as_bad(_("Condition \"%s\" uses a different accumulator from a preceding condition"), operand->buf);
                return 0;
            }
            if ((word & CATG_A1) && (cc_val & CATG_A1)) {
                as_bad(_("Only one comparison conditional allowed"));
                return 0;
            }
            if ((word & CATG_B1) && (cc_val & CATG_B1)) {
                as_bad(_("Only one overflow conditional allowed"));
                return 0;
            }
        } else {
            if (((word & CATG_A2) && (cc_val & CATG_A2)) ||
                ((word & CATG_B2) && (cc_val & CATG_B2)) ||
                ((word & CATG_C2) && (cc_val & CATG_C2))) {
                as_bad(_("Duplicate %s conditional"), operand->buf);
                return 0;
            }
        }
    }

    insn->opcode[0].word |= cc_val;
    return 1;
}

static int encode_cc3(tic54x_insn *insn, struct opstruct *operand) {
    tic54x_symbol *cc3;
    int value;

    if (insn == NULL || operand == NULL)
        return 0;

    cc3 = str_hash_find(cc3_hash, operand->buf);
    if (cc3)
        value = cc3->value;
    else
        value = operand->exp.X_add_number << 8;

    if ((value & 0x0300) != value) {
        as_bad(_("Unrecognized condition code \"%s\""), operand->buf ? operand->buf : "(null)");
        return 0;
    }

    if (insn->opcode == NULL)
        return 0;

    insn->opcode[0].word |= value;
    return 1;
}

static int encode_arx(tic54x_insn *insn, struct opstruct *operand)
{
    if (!operand || !operand->buf)
    {
        as_bad(_("Operand or buffer is NULL"));
        return 0;
    }

    if (strncmp(operand->buf, "ar", 2) != 0 && strncmp(operand->buf, "AR", 2) != 0)
    {
        as_bad(_("Invalid auxiliary register (use AR0-AR7)"));
        return 0;
    }

    if (strlen(operand->buf) < 3 || operand->buf[2] < '0' || operand->buf[2] > '7')
    {
        as_bad(_("Invalid auxiliary register (use AR0-AR7)"));
        return 0;
    }

    int arf = operand->buf[2] - '0';
    insn->opcode[0].word |= arf;
    return 1;
}

static int encode_cc2(tic54x_insn *insn, struct opstruct *operand)
{
    if (!insn || !operand || !operand->buf)
        return 0;

    tic54x_symbol *cc2 = str_hash_find(cc2_hash, operand->buf);
    if (!cc2) {
        as_bad(_("Unrecognized condition code \"%s\""), operand->buf);
        return 0;
    }
    insn->opcode[0].word |= cc2->value;
    return 1;
}

static int encode_operand(tic54x_insn *insn, enum optype type, struct opstruct *operand)
{
    int ext = (insn->tm->flags & FL_EXT) != 0;

    if (type == OP_MMR && operand->exp.X_op != O_constant) {
        if (insn->is_lkaddr) {
            as_bad(_("lk addressing modes are invalid for memory-mapped register addressing"));
            return 0;
        }
        type = OP_Smem;
        if (strncasecmp(operand->buf, "*+ar", 4) == 0) {
            as_warn(_("Address mode *+ARx is not allowed in memory-mapped register addressing. Resulting behavior is undefined."));
        }
    }

    switch (type) {
        case OP_None:
        case OP_B:
        case OP_A:
        case OP_16:
        case OP_T:
        case OP_TS:
        case OP_ASM:
        case OP_TRN:
        case OP_DP:
        case OP_ARP:
            return 1;

        case OP_dmad:
            return encode_dmad(insn, operand, 0);

        case OP_SRC: {
            char ch = TOUPPER(*operand->buf);
            int idx = ext ? (1 + insn->is_lkaddr) : 0;
            if (ch == 'B') {
                insn->opcode[idx].word |= (1 << 9);
                if (insn->using_default_dst)
                    insn->opcode[idx].word |= (1 << 8);
            }
            return 1;
        }

        case OP_RND: {
            int srcB = (TOUPPER(operand->buf[0]) == 'B');
            int dst8 = (insn->opcode[0].word & (1 << 8)) != 0;
            if (!(srcB ^ dst8)) {
                as_bad(_("Destination accumulator for each part of this parallel instruction must be different"));
                return 0;
            }
            return 1;
        }

        case OP_SRC1:
        case OP_DST: {
            char ch = TOUPPER(operand->buf[0]);
            int idx = ext ? (1 + insn->is_lkaddr) : 0;
            if (ch == 'B')
                insn->opcode[idx].word |= (1 << 8);
            return 1;
        }

        case OP_Xmem:
        case OP_Ymem: {
            int mod = (operand->buf[4] == '\0') ? 0 :
                      (operand->buf[4] == '-') ? 1 :
                      (operand->buf[5] == '\0') ? 2 : 3;
            int arf = operand->buf[3] - '0' - 2;
            int code = (mod << 2) | arf;
            int shift = (type == OP_Xmem) ? 4 : 0;
            insn->opcode[0].word |= (code << shift);
            return 1;
        }

        case OP_Lmem:
        case OP_Smem:
            if (!is_indirect(operand))
                return encode_address(insn, operand);
            return encode_indirect(insn, operand);

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

        case OP_MMR:
        case OP_MMRX:
        case OP_MMRY: {
            int value = operand->exp.X_add_number;
            if (type == OP_MMR) {
                insn->opcode[0].word |= value;
            } else {
                if (value < 16 || value > 24) {
                    as_bad(_("Memory mapped register \"%s\" out of range"), operand->buf);
                    return 0;
                }
                if (type == OP_MMRX)
                    insn->opcode[0].word |= (value - 16) << 4;
                else
                    insn->opcode[0].word |= (value - 16);
            }
            return 1;
        }

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

        case OP_123: {
            int value = operand->exp.X_add_number;
            int code;
            if (value < 1 || value > 3) {
                as_bad(_("Invalid operand (use 1, 2, or 3)"));
                return 0;
            }
            code = (value == 1) ? 0 : (value == 2) ? 0x2 : 0x1;
            insn->opcode[0].word |= (code << 8);
            return 1;
        }

        case OP_031:
            return encode_integer(insn, operand, 0, 0, 31, 0x1F);

        case OP_k8u:
            return encode_integer(insn, operand, 0, 0, 255, 0xFF);

        case OP_lku:
            return encode_integer(insn, operand, 1 + insn->is_lkaddr, 0, 65535, 0xFFFF);

        case OP_SBIT: {
            tic54x_symbol *sbit = str_hash_find(sbit_hash, operand->buf);
            int value = is_absolute(operand) ? operand->exp.X_add_number : (sbit ? sbit->value : -1);
            int reg = 0;
            if (insn->opcount == 1) {
                if (!sbit) {
                    as_bad(_("A status register or status bit name is required"));
                    return 0;
                }
                if (sbit > (tic54x_symbol *)str_hash_find(sbit_hash, "ovb"))
                    reg = 1;
            }
            if (value == -1) {
                as_bad(_("Unrecognized status bit \"%s\""), operand->buf);
                return 0;
            }
            insn->opcode[0].word |= value;
            insn->opcode[0].word |= (reg << 9);
            return 1;
        }

        case OP_N: {
            if (strcasecmp(operand->buf, "st0") == 0 || strcasecmp(operand->buf, "st1") == 0) {
                insn->opcode[0].word |= ((uint16_t)(operand->buf[2] - '0')) << 9;
                return 1;
            }
            if (operand->exp.X_op == O_constant && (operand->exp.X_add_number == 0 || operand->exp.X_add_number == 1)) {
                insn->opcode[0].word |= ((uint16_t)(operand->exp.X_add_number)) << 9;
                return 1;
            }
            as_bad(_("Invalid status register \"%s\""), operand->buf);
            return 0;
        }

        case OP_k5:
            return encode_integer(insn, operand, 0, -16, 15, 0x1F);

        case OP_k3:
            return encode_integer(insn, operand, 0, 0, 7, 0x7);

        case OP_k9:
            return encode_integer(insn, operand, 0, 0, 0x1FF, 0x1FF);

        case OP_12:
            if (operand->exp.X_add_number != 1 && operand->exp.X_add_number != 2) {
                as_bad(_("Operand \"%s\" out of range (use 1 or 2)"), operand->buf);
                return 0;
            }
            insn->opcode[0].word |= (operand->exp.X_add_number - 1) << 9;
            return 1;

        default:
            return 0;
    }
}

static void emit_insn(tic54x_insn *insn) {
    int i;
    flagword oldflags = bfd_section_flags(now_seg);
    flagword flags = oldflags | SEC_CODE;

    if (!bfd_set_section_flags(now_seg, flags)) {
        as_warn(_("error setting flags for \"%s\": %s"),
                bfd_section_name(now_seg),
                bfd_errmsg(bfd_get_error()));
    }

    for (i = 0; i < insn->words; ++i) {
        int unresolved = insn->opcode[i].unresolved;
        int r_type = insn->opcode[i].r_type;
        int size = (unresolved && r_type == BFD_RELOC_TIC54X_23) ? 4 : 2;
        char *p = frag_more(size);
        valueT value = (size == 2) ? insn->opcode[i].word
                                   : ((valueT)insn->opcode[i].word << 16);

        md_number_to_chars(p, value, size);

        if (unresolved) {
            fix_new_exp(frag_now, (int)(p - frag_now->fr_literal),
                        insn->opcode[i].r_nchars, &insn->opcode[i].addr_expr,
                        false, r_type);
        }
    }
}

/* Convert the operand strings into appropriate opcode values
   return the total number of words used by the instruction.  */

static int build_insn(tic54x_insn *insn)
{
    int i;
    int is_parallel = (insn->tm->flags & FL_PAR) != 0;

    insn->is_lkaddr = 0;
    insn->lkoperand = -1;

    if (!is_parallel) {
        for (i = 0; i < insn->opcount; i++) {
            int optype = OPTYPE(insn->operands[i].type);
            const char *opbuf = insn->operands[i].buf;

            if ((optype == OP_Smem || optype == OP_Lmem || optype == OP_Sind)
                && strchr(opbuf, '(')
                && strncasecmp(opbuf, "*sp (", 4) != 0) 
            {
                insn->is_lkaddr = 1;
                insn->lkoperand = i;
                break;
            }
        }
    }

    insn->words = insn->tm->words + insn->is_lkaddr;

    if (insn->words > (int)(sizeof(insn->opcode)/sizeof(insn->opcode[0])))
        return 0;

    insn->opcode[0].word = insn->tm->opcode;

    if (insn->tm->flags & FL_EXT) {
        int idx = 1 + insn->is_lkaddr;
        if (idx >= (int)(sizeof(insn->opcode)/sizeof(insn->opcode[0])))
            return 0;
        insn->opcode[idx].word = insn->tm->opcode2;
    }

    for (i = 0; i < insn->opcount; i++) {
        if (!encode_operand(insn, insn->operands[i].type, &insn->operands[i]))
            return 0;
    }

    if (is_parallel) {
        for (i = 0; i < insn->paropcount; i++) {
            if (!encode_operand(insn, insn->paroperands[i].type, &insn->paroperands[i]))
                return 0;
        }
    }

    emit_insn(insn);
    return insn->words;
}

static int optimize_insn(tic54x_insn *insn)
{
#define is_zero(op) ((op).exp.X_op == O_constant && (op).exp.X_add_number == 0)
    int ret = 0;
    const char *name;
    if (!insn || !insn->tm || !insn->tm->name)
        return 0;
    name = insn->tm->name;

    if (strcasecmp(name, "add") == 0) {
        if (insn->opcount > 1 &&
            is_accumulator(&insn->operands[insn->opcount - 2]) &&
            is_accumulator(&insn->operands[insn->opcount - 1]) &&
            strcasecmp(insn->operands[insn->opcount - 2].buf, insn->operands[insn->opcount - 1].buf) == 0) {
            insn->opcount--;
            insn->using_default_dst = 1;
            return 1;
        }
        if (insn->opcount > 2) {
            int type0 = OPTYPE(insn->tm->operand_types[0]);
            int type1 = OPTYPE(insn->tm->operand_types[1]);
            if ((type0 == OP_Xmem && type1 == OP_SHFT && is_zero(insn->operands[1])) ||
                (type0 == OP_Smem && type1 == OP_SHIFT &&
                is_type(&insn->operands[1], OP_SHIFT) &&
                is_zero(insn->operands[1]) && insn->opcount == 3)) {
                insn->operands[1] = insn->operands[2];
                insn->opcount = 2;
                return 1;
            }
        }
    } else if (strcasecmp(name, "ld") == 0) {
        if (insn->opcount == 3 && insn->operands[0].type != OP_SRC) {
            int type1 = OPTYPE(insn->tm->operand_types[1]);
            int type0 = OPTYPE(insn->tm->operand_types[0]);
            if ((type1 == OP_SHIFT || type1 == OP_SHFT) &&
                is_zero(insn->operands[1]) &&
                (type0 != OP_lk ||
                (insn->operands[0].exp.X_op == O_constant &&
                 insn->operands[0].exp.X_add_number >= 0 &&
                 insn->operands[0].exp.X_add_number <= 255))) {
                insn->operands[1] = insn->operands[2];
                insn->opcount = 2;
                return 1;
            }
        }
    } else if (strcasecmp(name, "sth") == 0 || strcasecmp(name, "stl") == 0) {
        if (insn->opcount > 2) {
            int type1 = OPTYPE(insn->tm->operand_types[1]);
            if ((type1 == OP_SHIFT || type1 == OP_SHFT) && is_zero(insn->operands[1])) {
                insn->operands[1] = insn->operands[2];
                insn->opcount = 2;
                return 1;
            }
        }
    } else if (strcasecmp(name, "sub") == 0) {
        if (insn->opcount > 1 &&
            is_accumulator(&insn->operands[insn->opcount - 2]) &&
            is_accumulator(&insn->operands[insn->opcount - 1]) &&
            strcasecmp(insn->operands[insn->opcount - 2].buf, insn->operands[insn->opcount - 1].buf) == 0) {
            insn->opcount--;
            insn->using_default_dst = 1;
            return 1;
        }
        if (insn->opcount == 3) {
            int type0 = OPTYPE(insn->tm->operand_types[0]);
            int type1 = OPTYPE(insn->tm->operand_types[1]);
            if (((type0 == OP_Smem && type1 == OP_SHIFT) ||
                 (type0 == OP_Xmem && type1 == OP_SHFT)) &&
                 is_zero(insn->operands[1])) {
                insn->operands[1] = insn->operands[2];
                insn->opcount = 2;
                return 1;
            }
        }
    }
    return ret;
}

/* Find a matching template if possible, and get the operand strings.  */

static int
tic54x_parse_insn(tic54x_insn *insn, char *line)
{
    if (!insn || !insn->mnemonic || !line)
        return 0;

    insn->tm = str_hash_find(op_hash, insn->mnemonic);
    if (!insn->tm) {
        as_bad(_("Unrecognized instruction \"%s\""), insn->mnemonic);
        return 0;
    }

    insn->opcount = get_operands(insn->operands, line);
    if (insn->opcount < 0)
        return 0;

    tic54x_template *tm = insn->tm;
    while (tm && tm->name && strcasecmp(tm->name, insn->mnemonic) == 0) {
        if (
            insn->opcount >= tm->minops &&
            insn->opcount <= tm->maxops &&
            operands_match(insn, &insn->operands[0], insn->opcount,
                           tm->operand_types,
                           tm->minops, tm->maxops)
        ) {
            if (optimize_insn(insn)) {
                tm = str_hash_find(op_hash, insn->mnemonic);
                if (!tm)
                    break;
                continue;
            }
            insn->tm = tm;
            return 1;
        }
        ++tm;
    }
    as_bad(_("Unrecognized operand list '%s' for instruction '%s'"),
           line, insn->mnemonic);
    return 0;
}

/* We set this in start_line_hook, 'cause if we do a line replacement, we
   won't be able to see the next line.  */
static int parallel_on_next_line_hint = 0;

/* See if this is part of a parallel instruction
   Look for a subsequent line starting with "||".  */

static int next_line_shows_parallel(const char *next_line)
{
    if (!next_line) {
        return 0;
    }
    while (*next_line && (is_whitespace(*next_line) || is_end_of_stmt(*next_line))) {
        next_line++;
    }
    return (*next_line == PARALLEL_SEPARATOR && *(next_line + 1) == PARALLEL_SEPARATOR);
}

static int tic54x_parse_parallel_insn_firstline(tic54x_insn *insn, char *line)
{
    if (!insn || !line || !insn->mnemonic) {
        return 0;
    }

    insn->tm = str_hash_find(parop_hash, insn->mnemonic);
    if (!insn->tm) {
        as_bad(_("Unrecognized parallel instruction \"%s\""), insn->mnemonic);
        return 0;
    }

    for (; insn->tm->name && strcasecmp(insn->tm->name, insn->mnemonic) == 0; ++(insn->tm)) {
        insn->opcount = get_operands(insn->operands, line);
        if (insn->opcount < 0) {
            return 0;
        }
        if (insn->opcount == 2 &&
            operands_match(insn, &insn->operands[0], insn->opcount,
                          insn->tm->operand_types, 2, 2)) {
            return 1;
        }
    }
    return 0;
}

/* Parse the second line of a two-line parallel instruction.  */

static int tic54x_parse_parallel_insn_lastline(tic54x_insn *insn, char *line) {
    int valid_mnemonic = 0;

    if (!insn || !line) {
        as_bad(_("Null pointer argument to tic54x_parse_parallel_insn_lastline"));
        return 0;
    }

    insn->paropcount = get_operands(insn->paroperands, line);

    while (insn->tm && insn->tm->name) {
        if (strcasecmp(insn->tm->name, insn->mnemonic) == 0) {
            if (strcasecmp(insn->tm->parname, insn->parmnemonic) == 0) {
                valid_mnemonic = 1;
                if (insn->paropcount >= insn->tm->minops &&
                    insn->paropcount <= insn->tm->maxops &&
                    operands_match(insn, insn->paroperands, insn->paropcount,
                                   insn->tm->paroperand_types,
                                   insn->tm->minops, insn->tm->maxops)) {
                    return 1;
                }
            }
        }
        insn->tm++;
    }

    if (valid_mnemonic) {
        as_bad(_("Invalid operand(s) for parallel instruction \"%s\""), insn->parmnemonic);
    } else {
        as_bad(_("Unrecognized parallel instruction combination \"%s || %s\""),
               insn->mnemonic ? insn->mnemonic : "(null)",
               insn->parmnemonic ? insn->parmnemonic : "(null)");
    }
    return 0;
}

/* If quotes found, return copy of line up to closing quote;
   otherwise up until terminator.
   If it's a string, pass as-is; otherwise attempt substitution symbol
   replacement on the value.  */

static char *
subsym_get_arg(char *line, const char *terminators, char **str, int nosub)
{
    if (line == NULL || str == NULL || terminators == NULL) {
        return NULL;
    }

    char *ptr = line;
    char *endp = NULL;

    if (*line == '\0') {
        *str = xmemdup0("", 0);
        return line;
    }

    if (ISDIGIT(*line)) {
        while (ISDIGIT(*ptr)) {
            ++ptr;
        }
        endp = ptr;
        *str = xmemdup0(line, ptr - line);
        return endp;
    }

    if (*line == '"') {
        char *savedp = input_line_pointer;
        int len = 0;

        input_line_pointer = ptr;
        *str = demand_copy_C_string(&len);
        endp = input_line_pointer;
        input_line_pointer = savedp;

        if (*str == NULL) {
            return NULL;
        }

        if (!nosub && **str == ':') {
            char *subst = subsym_substitute(*str, 1);
            if (subst) {
                *str = subst;
            }
        }
        return endp;
    }

    /* Non-string, non-digit: parse up to any terminator. */
    ptr = line;
    while (*ptr) {
        const char *term = terminators;
        int is_term = 0;
        while (*term) {
            if (*ptr == *term) {
                is_term = 1;
                break;
            }
            ++term;
        }
        if (is_term) {
            break;
        }
        ++ptr;
    }
    endp = ptr;

    *str = xmemdup0(line, ptr - line);

    if (*str == NULL) {
        return NULL;
    }

    if (!nosub) {
        subsym_ent_t *ent = subsym_lookup(*str, macro_level);
        if (ent && !ent->isproc && ent->u.s != NULL) {
            *str = ent->u.s;
        }
    }

    return endp;
}

/* Replace the given substitution string.
   We start at the innermost macro level, so that existing locals remain local
   Note: we're treating macro args identically to .var's; I don't know if
   that's compatible w/TI's assembler.  */

static void subsym_create_or_replace(char *name, char *value) {
    if (!name || !value) {
        return;
    }

    subsym_ent_t *ent = xmalloc(sizeof(*ent));
    if (!ent) {
        return;
    }

    ent->u.s = value;
    ent->freekey = 0;
    ent->freeval = 0;
    ent->isproc = 0;
    ent->ismath = 0;

    for (int i = macro_level; i > 0; i--) {
        if (str_hash_find(subsym_hash[i], name)) {
            str_hash_insert(subsym_hash[i], name, ent, 1);
            return;
        }
    }
    str_hash_insert(subsym_hash[0], name, ent, 1);
}

/* Look up the substitution string replacement for the given symbol.
   Start with the innermost macro substitution table given and work
   outwards.  */

static subsym_ent_t *subsym_lookup(const char *name, int nest_level)
{
    if (name == NULL || nest_level < 0)
        return NULL;

    do {
        void *value = str_hash_find(subsym_hash[nest_level], name);
        if (value)
            return value;
    } while (--nest_level >= 0);

    return NULL;
}

/* Do substitution-symbol replacement on the given line (recursively).
   return the argument if no substitution was done

   Also look for built-in functions ($func (arg)) and local labels.

   If FORCED is set, look for forced substitutions of the form ':SYMBOL:'.  */

static char *
subsym_substitute(char *line, int forced)
{
    char *replacement, *head, *ptr, *tmp;
    char current_char;
    int changed = 0, eval_line = 0, eval_symbol = 0, recurse, line_conditional = 0;
    char *eval_end = NULL;

    if (strstr(line, ".if") || strstr(line, ".elseif") || strstr(line, ".break"))
        line_conditional = 1;

    if (strstr(line, ".eval") || strstr(line, ".asg"))
        eval_line = 1;

    if (strstr(line, ".macro"))
        return line;

    replacement = xstrdup(line);
    head = ptr = replacement;

    while (!is_end_of_stmt(current_char = *ptr)) {
        recurse = 1;

        if (eval_line)
            eval_end = strrchr(ptr, ',');

        if (current_char == '"' && ptr[1] == '"' && ptr[2] == '"') {
            ptr[1] = '\\';
            tmp = strstr(ptr + 2, "\"\"\"");
            if (tmp)
                tmp[0] = '\\';
            changed = 1;
        }

        if (line_conditional && current_char == '=') {
            if (ptr[1] == '=') {
                ptr += 2;
                continue;
            }
            *ptr++ = '\0';
            tmp = concat(head, "==", ptr, (char *)NULL);
            ptr = tmp + strlen(head) + 2;
            free(replacement);
            head = replacement = tmp;
            changed = 1;
            continue;
        }

        if (eval_line && ptr >= eval_end)
            eval_symbol = 1;

        if ((forced && current_char == ':') || (!forced && is_name_beginner(current_char))) {
            char *name = NULL;
            char *savedp = input_line_pointer;
            int c;
            subsym_ent_t *ent = NULL;
            char *value = NULL;
            char *tail;
            int symbol_recursed = 0;

            if (forced)
                ++ptr;

            input_line_pointer = ptr;
            c = get_symbol_name(&name);

            if (c == '?') {
                *input_line_pointer++ = c;
                c = *input_line_pointer;
                *input_line_pointer = '\0';
            }

            if (str_hash_find(subsym_recurse_hash, name) == NULL) {
                ent = subsym_lookup(name, macro_level);
                if (ent && !ent->isproc)
                    value = ent->u.s;
            } else {
                as_warn(_("%s symbol recursion stopped at second appearance of '%s'"),
                        forced ? "Forced substitution" : "Substitution", name);
                symbol_recursed = 1;
            }
            ptr = tail = input_line_pointer;
            input_line_pointer = savedp;

            if ((*name == '$' && ISDIGIT(name[1]) && name[2] == '\0') ||
                name[strlen(name) - 1] == '?') {
                value = str_hash_find(local_label_hash[macro_level], name);
                if (value == NULL) {
                    char digit[11];
                    char *namecopy = xstrdup(name);
                    value = xmalloc(strlen(name) + sizeof(digit) + 1);
                    strcpy(value, name);
                    if (*value != '$')
                        value[strlen(value) - 1] = '\0';
                    sprintf(digit, ".%d", local_label_id++);
                    strcat(value, digit);
                    str_hash_insert(local_label_hash[macro_level], namecopy, value, 0);
                }
                ptr = tail;
            } else if (ent != NULL && *name == '$') {
                const subsym_proc_entry *entry = ent->u.p;
                char *arg1 = NULL, *arg2 = NULL;
                *ptr = c;
                if (!ent->isproc) {
                    as_bad(_("Unrecognized substitution symbol function"));
                    free(name);
                    break;
                } else if (*ptr != '(') {
                    as_bad(_("Missing '(' after substitution symbol function"));
                    free(name);
                    break;
                }
                ++ptr;
                if (ent->ismath) {
                    float farg1, farg2 = 0.0f;
                    farg1 = (float)strtod(ptr, &ptr);
                    if (entry->nargs == 2) {
                        if (*ptr++ != ',') {
                            as_bad(_("Expecting second argument"));
                            free(name);
                            break;
                        }
                        farg2 = (float)strtod(ptr, &ptr);
                    }
                    value = XNEWVEC(char, 128);
                    if (entry->type == 2)
                        sprintf(value, "%d", (*entry->proc.i)(farg1, farg2));
                    else
                        sprintf(value, "%f", (*entry->proc.f)(farg1, farg2));
                    if (*ptr++ != ')') {
                        as_bad(_("Extra junk in function call, expecting ')'"));
                        free(name);
                        break;
                    }
                    recurse = 0;
                } else {
                    int val;
                    int arg_type[2] = { *ptr == '"', 0 };
                    int ismember = !strcmp(entry->name, "$ismember");
                    ptr = subsym_get_arg(ptr, ",)", &arg1, ismember);
                    if (!arg1) {
                        free(name);
                        break;
                    }
                    if (entry->nargs == 2) {
                        if (*ptr++ != ',') {
                            as_bad(_("Function expects two arguments"));
                            free(arg1);
                            free(name);
                            break;
                        }
                        arg_type[1] = (ISDIGIT(*ptr)) ? 2 : (*ptr == '"');
                        ptr = subsym_get_arg(ptr, ")", &arg2, ismember);
                        if (!arg2) {
                            free(arg1);
                            free(name);
                            break;
                        }
                    }
                    if ((!strcmp(entry->name, "$firstch") ||
                         !strcmp(entry->name, "$lastch")) && arg_type[1] != 2) {
                        as_bad(_("Expecting character constant argument"));
                        free(arg1); free(arg2); free(name);
                        break;
                    }
                    if (ismember && (arg_type[0] != 0 || arg_type[1] != 0)) {
                        as_bad(_("Both arguments must be substitution symbols"));
                        free(arg1); free(arg2); free(name);
                        break;
                    }
                    if (*ptr++ != ')') {
                        as_bad(_("Extra junk in function call, expecting ')'"));
                        free(arg1); free(arg2); free(name);
                        break;
                    }
                    val = (*entry->proc.s)(arg1, arg2);
                    value = XNEWVEC(char, 64);
                    sprintf(value, "%d", val);
                    free(arg1); free(arg2);
                }
                tail = ptr;
                c = *tail;
            }

            if (value != NULL && !eval_symbol && !symbol_recursed) {
                if (recurse) {
                    str_hash_insert(subsym_recurse_hash, name, name, 0);
                    char *recursive_value = subsym_substitute(value, macro_level > 0);
                    if (recursive_value != value) {
                        free(value);
                        value = recursive_value;
                    }
                    str_hash_delete(subsym_recurse_hash, name);
                }
                *name = 0;
                if (forced) {
                    if (c == '(') {
                        unsigned beg, len = 1;
                        char *newval = xstrdup(value);

                        savedp = input_line_pointer;
                        input_line_pointer = tail + 1;
                        beg = get_absolute_expression();
                        if (beg < 1) {
                            as_bad(_("Invalid subscript (use 1 to %d)"),
                                   (int)strlen(value));
                            free(name);
                            free(newval);
                            break;
                        }
                        if (*input_line_pointer == ',') {
                            ++input_line_pointer;
                            len = get_absolute_expression();
                            if (beg + len > strlen(value)) {
                                as_bad(_("Invalid length (use 0 to %d)"),
                                       (int)strlen(value) - beg);
                                free(name);
                                free(newval);
                                break;
                            }
                        }
                        newval += beg - 1;
                        newval[len] = 0;
                        tail = input_line_pointer;
                        if (*tail++ != ')') {
                            as_bad(_("Missing ')' in subscripted substitution symbol expression"));
                            free(name);
                            break;
                        }
                        c = *tail;
                        input_line_pointer = savedp;
                        value = newval;
                    }
                    name[-1] = 0;
                }
                tmp = xmalloc(strlen(head) + strlen(value) + strlen(tail + 1) + 2);
                strcpy(tmp, head);
                strcat(tmp, value);
                if (forced) {
                    if (c != ':') {
                        as_bad(_("Missing forced substitution terminator ':'"));
                        free(name);
                        free(tmp);
                        break;
                    }
                    ++tail;
                } else
                    *tail = c;
                strcat(tmp, tail);
                ptr = tmp + strlen(head) + strlen(value);
                free(replacement);
                head = replacement = tmp;
                changed = 1;
                if (value != NULL && value != ent->u.s)
                    free(value);
            } else {
                *ptr = c;
            }
            free(name);
        } else {
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

void tic54x_start_line_hook(void) {
    char *line = NULL, *endp = NULL;
    char *replacement = NULL;

    endp = input_line_pointer;
    while (*endp) {
        if (is_end_of_stmt(*endp++))
            break;
    }

    line = xmemdup0(input_line_pointer, endp - input_line_pointer);

    parallel_on_next_line_hint = next_line_shows_parallel(endp);

    if (macro_level > 0)
        replacement = subsym_substitute(line, 1);
    else
        replacement = line;
    replacement = subsym_substitute(replacement, 0);

    if (replacement != line) {
        char *tmp = replacement;
        char *comment = strchr(replacement, ';');
        size_t len = strlen(replacement);
        char endc = (len > 0) ? replacement[len - 1] : '\0';

        if (comment) {
            comment[0] = endc;
            comment[1] = '\0';
            --comment;
        } else if (len > 0) {
            comment = replacement + len - 1;
        } else {
            comment = replacement;
        }

        while (comment > replacement && is_whitespace(*comment)) {
            *comment = endc;
            comment[1] = '\0';
            --comment;
        }

        while (tmp[0] && is_whitespace(tmp[0]) && is_whitespace(tmp[1]))
            ++tmp;

        input_line_pointer = endp;
        input_scrub_insert_line(tmp);

        if (replacement != line)
            free(replacement);
        free(line);
        substitution_line = 1;
    } else {
        free(line);
        substitution_line = 0;
    }
}

/* This is the guts of the machine-dependent assembler.  STR points to a
   machine dependent instruction.  This function is supposed to emit
   the frags/bytes it assembles to.  */
void md_assemble(char *line)
{
    static int repeat_slot = 0;
    static int delay_slots = 0;
    static int is_parallel = 0;
    static tic54x_insn insn;
    char *lptr;
    char *savedp = input_line_pointer;
    int c;
    char *parallel_marker = NULL;

    input_line_pointer = line;
    c = get_symbol_name(&line);

    if (cpu == VNONE)
        cpu = V542;

    if (address_mode_needs_set) {
        set_address_mode(amode);
        address_mode_needs_set = 0;
    }
    if (cpu_needs_set) {
        set_cpu(cpu);
        cpu_needs_set = 0;
    }

    assembly_begun = 1;

    if (is_parallel) {
        is_parallel = 0;

        if (strncpy(insn.parmnemonic, line, sizeof(insn.parmnemonic) - 1) == NULL)
            return;

        insn.parmnemonic[sizeof(insn.parmnemonic) - 1] = '\0';
        lptr = input_line_pointer;
        *lptr = c;
        input_line_pointer = savedp;

        if (tic54x_parse_parallel_insn_lastline(&insn, lptr)) {
            int words = build_insn(&insn);

            if (delay_slots > 0) {
                if (words > delay_slots) {
                    as_bad(ngettext(
                        "Instruction does not fit in available delay slots (%d-word insn, %d slot left)",
                        "Instruction does not fit in available delay slots (%d-word insn, %d slots left)",
                        delay_slots), words, delay_slots);
                    delay_slots = 0;
                    return;
                }
                delay_slots -= words;
            }
        }
        return;
    }

    memset(&insn, 0, sizeof(insn));
    if (strncpy(insn.mnemonic, line, sizeof(insn.mnemonic) - 1) == NULL)
        return;
    insn.mnemonic[sizeof(insn.mnemonic) - 1] = '\0';
    lptr = input_line_pointer;
    *lptr = c;
    input_line_pointer = savedp;

    parallel_marker = strstr(line, "||");

    if (parallel_marker != NULL || parallel_on_next_line_hint) {
        char *tmp = parallel_marker;
        if (tmp != NULL)
            *tmp = '\0';

        if (tic54x_parse_parallel_insn_firstline(&insn, lptr)) {
            is_parallel = 1;
            if (tmp != NULL) {
                tmp += 2;
                while (*tmp != '\0' && is_whitespace(*tmp))
                    tmp++;
                md_assemble(tmp);
            }
        } else {
            as_bad(_("Unrecognized parallel instruction '%s'"), line);
        }
        return;
    }

    if (tic54x_parse_insn(&insn, lptr)) {
        int words;

        if ((insn.tm->flags & FL_LP) && cpu != V545LP && cpu != V546LP) {
            as_bad(_("Instruction '%s' requires an LP cpu version"), insn.tm->name);
            return;
        }
        if ((insn.tm->flags & FL_FAR) && amode != far_mode) {
            as_bad(_("Instruction '%s' requires far mode addressing"), insn.tm->name);
            return;
        }

        words = build_insn(&insn);

        if (delay_slots > 0) {
            if (words > delay_slots) {
                as_warn(ngettext(
                    "Instruction does not fit in available delay slots (%d-word insn, %d slot left). Resulting behavior is undefined.",
                    "Instruction does not fit in available delay slots (%d-word insn, %d slots left). Resulting behavior is undefined.",
                    delay_slots), words, delay_slots);
                delay_slots = 0;
                return;
            }
            if (insn.tm->flags & FL_BMASK) {
                as_warn(_("Instructions which cause PC discontinuity are not allowed in a delay slot. Resulting behavior is undefined."));
            }
            delay_slots -= words;
        }

        if (repeat_slot) {
            if (insn.tm->flags & FL_NR)
                as_warn(_("'%s' is not repeatable. Resulting behavior is undefined."), insn.tm->name);
            else if (insn.is_lkaddr)
                as_warn(_("Instructions using long offset modifiers or absolute addresses are not repeatable. Resulting behavior is undefined."));
            repeat_slot = 0;
        }

        if (insn.tm->flags & B_REPEAT) {
            repeat_slot = 1;
        }
        if (insn.tm->flags & FL_DELAY) {
            delay_slots = 2;
        }
    }
}

/* Do a final adjustment on the symbol table; in this case, make sure we have
   a ".file" symbol.  */

void tic54x_adjust_symtab(void)
{
    if (!symbol_rootP || S_GET_STORAGE_CLASS(symbol_rootP) != C_FILE)
    {
        unsigned lineno;
        const char *filename = as_where(&lineno);
        if (filename)
        {
            c_dot_file_symbol(filename);
        }
    }
}

/* In order to get gas to ignore any | chars at the start of a line,
   this function returns true if a | is found in a line.
   This lets us process parallel instructions, which span two lines.  */

int tic54x_unrecognized_line(int c) {
    return (c == PARALLEL_SEPARATOR) ? 1 : 0;
}

/* Watch for local labels of the form $[0-9] and [_a-zA-Z][_a-zA-Z0-9]*?
   Encode their names so that only we see them and can map them to the
   appropriate places.
   FIXME -- obviously this isn't done yet.  These locals still show up in the
   symbol table.  */
void tic54x_define_label(symbolS *sym) {
    if (sym == NULL) {
        return;
    }
    last_label_seen = sym;
}

/* Try to parse something that normal parsing failed at.  */

symbolS *tic54x_undefined_symbol(char *name) {
    tic54x_symbol *sym = NULL;

    if (!name) {
        return NULL;
    }

    sym = str_hash_find(cc_hash, name);
    if (sym) goto create_symbol;
    sym = str_hash_find(cc2_hash, name);
    if (sym) goto create_symbol;
    sym = str_hash_find(cc3_hash, name);
    if (sym) goto create_symbol;
    if (str_hash_find(misc_symbol_hash, name)) {
        sym = NULL;
        goto create_symbol;
    }
    sym = str_hash_find(sbit_hash, name);
    if (sym) goto create_symbol;
    sym = str_hash_find(reg_hash, name);
    if (sym) goto create_symbol;
    sym = str_hash_find(mmreg_hash, name);
    if (sym) goto create_symbol;
    if (!strcasecmp(name, "a") || !strcasecmp(name, "b")) {
        sym = NULL;
        goto create_symbol;
    }

    return NULL;

create_symbol:
    return symbol_new(name, reg_section, &zero_address_frag, sym ? sym->value : 0);
}

/* Parse a name in an expression before the expression parser takes a stab at
   it.  */

int tic54x_parse_name(char *name, expressionS *expn)
{
    (void)name;
    (void)expn;
    return 0;
}

const char *md_atof(int type, char *literalP, int *sizeP) {
    return ieee_md_atof(type, literalP, sizeP, 1);
}

arelent *
tc_gen_reloc(asection *section, fixS *fixP)
{
  if (!section || !fixP || !fixP->fx_addsy || !fixP->fx_frag) 
    return NULL;

  arelent *rel = notes_alloc(sizeof(arelent));
  if (!rel)
    return NULL;

  rel->sym_ptr_ptr = notes_alloc(sizeof(asymbol *));
  if (!rel->sym_ptr_ptr) {
    free(rel);
    return NULL;
  }

  bfd_reloc_code_real_type code = fixP->fx_r_type;
  asymbol *sym = symbol_get_bfdsym(fixP->fx_addsy);
  if (!sym) {
    free(rel->sym_ptr_ptr);
    free(rel);
    return NULL;
  }
  *rel->sym_ptr_ptr = sym;

  rel->address = fixP->fx_frag->fr_address + fixP->fx_where;
  rel->address /= OCTETS_PER_BYTE;

  rel->howto = bfd_reloc_type_lookup(stdoutput, code);
  if (sym->name && section->name && strcmp(sym->name, section->name) == 0)
    rel->howto = rel->howto ? rel->howto + HOWTO_BANK : NULL;

  if (!rel->howto) {
    const char *name = S_GET_NAME(fixP->fx_addsy);
    if (!name)
      name = "<unknown>";
    as_fatal("Cannot generate relocation type for symbol %s, code %s",
             name, bfd_get_reloc_code_name(code));
    free(rel->sym_ptr_ptr);
    free(rel);
    return NULL;
  }

  return rel;
}

/* Handle cons expressions.  */

void tic54x_cons_fix_new(fragS *frag, int where, int octets, expressionS *expn, bfd_reloc_code_real_type r)
{
    switch (octets)
    {
        case 2:
            r = BFD_RELOC_TIC54X_16_OF_23;
            break;
        case 4:
            r = emitting_long ? BFD_RELOC_TIC54X_23 : BFD_RELOC_32;
            break;
        default:
            as_bad(_("Unsupported relocation size %d"), octets);
            r = BFD_RELOC_TIC54X_16_OF_23;
            break;
    }
    fix_new_exp(frag, where, octets, expn, 0, r);
}

/* Attempt to simplify or even eliminate a fixup.
   To indicate that a fixup has been eliminated, set fixP->fx_done.

   If fixp->fx_addsy is non-NULL, we'll have to generate a reloc entry.   */

void md_apply_fix(fixS *fixP, valueT *valP, segT seg ATTRIBUTE_UNUSED)
{
    if (fixP == NULL || valP == NULL || fixP->fx_frag == NULL) {
        as_fatal("Null pointer in md_apply_fix");
        return;
    }

    char *buf = fixP->fx_where + fixP->fx_frag->fr_literal;
    valueT val = *valP;

    switch (fixP->fx_r_type)
    {
        case BFD_RELOC_TIC54X_MS7_OF_23:
            val = (val >> 16) & 0x7F;
            /* fall-through */
        case BFD_RELOC_TIC54X_16_OF_23:
        case BFD_RELOC_16:
            bfd_put_16(stdoutput, val, buf);
            *valP = val & 0xFFFF;
            break;
        case BFD_RELOC_TIC54X_PARTLS7: {
            unsigned short orig = bfd_get_16(stdoutput, buf);
            unsigned short result = (orig & 0xFF80) | (val & 0x7F);
            bfd_put_16(stdoutput, result, buf);
            *valP = val & 0x7F;
            break;
        }
        case BFD_RELOC_TIC54X_PARTMS9: {
            unsigned short orig = bfd_get_16(stdoutput, buf);
            unsigned short result = (orig & 0xFE00) | ((val >> 7) & 0x1FF);
            bfd_put_16(stdoutput, result, buf);
            break;
        }
        case BFD_RELOC_32:
        case BFD_RELOC_TIC54X_23: {
            unsigned long orig = bfd_get_32(stdoutput, buf);
            unsigned long result = (orig & 0xFF800000) | (val & 0x7FFFFF);
            bfd_put_32(stdoutput, result, buf);
            break;
        }
        default:
            as_fatal("Bad relocation type: 0x%02x", fixP->fx_r_type);
            return;
    }

    if (fixP->fx_addsy == NULL && fixP->fx_pcrel == 0) {
        fixP->fx_done = 1;
    }
}

/* This is our chance to record section alignment
   don't need to do anything here, since BFD does the proper encoding.  */

valueT md_section_align(segT segment, valueT section_size) {
  (void)segment;
  return section_size;
}

long md_pcrel_from(fixS *fixP)
{
  (void)fixP;
  return 0;
}

/* Mostly little-endian, but longwords (4 octets) get MS word stored
   first.  */

void tic54x_number_to_chars(char *buf, valueT val, int n)
{
    if (buf == NULL || n <= 0)
        return;

    if (n == 4) {
        number_to_chars_littleendian(buf,     (val >> 16) & 0xFFFF, 2);
        number_to_chars_littleendian(buf + 2, val & 0xFFFF,        2);
    } else {
        number_to_chars_littleendian(buf, val, n);
    }
}

int tic54x_estimate_size_before_relax(fragS *frag, segT seg) {
    (void)frag;
    (void)seg;
    return 0;
}

/* We use this to handle bit allocations which we couldn't handle before due
   to symbols being in different frags.  return number of octets added.  */

int tic54x_relax_frag(fragS *frag, long stretch ATTRIBUTE_UNUSED)
{
    symbolS *sym = frag->fr_symbol;
    int growth = 0;

    if (sym == NULL) {
        return 0;
    }

    struct bit_info *bi = (struct bit_info *)frag->fr_opcode;
    int bit_offset = frag_bit_offset(frag_prev(frag, bi->seg), bi->seg);
    int size = S_GET_VALUE(sym);
    fragS *prev_frag = bit_offset_frag(frag_prev(frag, bi->seg), bi->seg);
    int available = 16 - bit_offset;

    if (symbol_get_frag(sym) != &zero_address_frag || S_IS_COMMON(sym) || !S_IS_DEFINED(sym)) {
        as_bad_where(frag->fr_file, frag->fr_line, _("non-absolute value used with .space/.bes"));
    }

    if (size < 0) {
        as_warn(_("negative value ignored in %s"), bi->type == TYPE_SPACE ? ".space" : bi->type == TYPE_BES ? ".bes" : ".field");
        growth = 0;
        frag->tc_frag_data = 0;
        frag->fr_fix = 0;
        return 0;
    }

    if (bi->type == TYPE_FIELD) {
        if (bit_offset != 0 && available >= size) {
            char *p = prev_frag->fr_literal;
            valueT value = bi->value;
            value <<= (available - size);
            value |= ((uint16_t)p[1] << 8) | (uint8_t)p[0];
            md_number_to_chars(p, value, 2);
            prev_frag->tc_frag_data += size;
            if (prev_frag->tc_frag_data == 16) {
                prev_frag->tc_frag_data = 0;
            }
            if (bi->sym) {
                symbol_set_frag(bi->sym, prev_frag);
            }
            growth = -frag->fr_fix;
            frag->fr_fix = 0;
            frag->tc_frag_data = 0;
        } else {
            char *p = frag->fr_literal;
            valueT value = bi->value << (16 - size);
            md_number_to_chars(p, value, 2);
            frag->tc_frag_data = size;
            if (frag->tc_frag_data == 16) {
                frag->tc_frag_data = 0;
            }
            growth = 0;
        }
    } else {
        if (bit_offset != 0 && bit_offset < 16) {
            if (available >= size) {
                prev_frag->tc_frag_data += size;
                if (prev_frag->tc_frag_data == 16) {
                    prev_frag->tc_frag_data = 0;
                }
                if (bi->sym) {
                    symbol_set_frag(bi->sym, prev_frag);
                }
                growth = -frag->fr_fix;
                frag->fr_fix = 0;
                frag->tc_frag_data = 0;
                goto cleanup;
            }
            if (bi->type == TYPE_SPACE && bi->sym) {
                symbol_set_frag(bi->sym, prev_frag);
            }
            size -= available;
        }
        growth = ((size + 15) / 16) * OCTETS_PER_BYTE - frag->fr_fix;
        for (int i = 0; i < growth; i++) {
            frag->fr_literal[i] = 0;
        }
        frag->fr_fix = growth;
        frag->tc_frag_data = size % 16;
        if (bi->type == TYPE_BES && bi->sym) {
            S_SET_VALUE(bi->sym, frag->fr_fix / OCTETS_PER_BYTE - 1);
        }
    }

cleanup:
    frag->fr_symbol = NULL;
    frag->fr_opcode = NULL;
    free(bi);

    return growth;
}


void tic54x_convert_frag(bfd *abfd ATTRIBUTE_UNUSED, segT seg ATTRIBUTE_UNUSED, fragS *frag) {
    if (frag == NULL || frag->fr_next == NULL || frag->fr_var == 0) {
        as_bad_where(frag ? frag->fr_file : NULL, frag ? frag->fr_line : 0,
                     _("invalid fragment or division by zero in tic54x_convert_frag"));
        return;
    }

    long delta = (long)frag->fr_next->fr_address - (long)frag->fr_address - (long)frag->fr_fix;
    frag->fr_offset = delta / frag->fr_var;

    if (frag->fr_offset < 0) {
        as_bad_where(frag->fr_file, frag->fr_line,
                     _("attempt to .space/.bes backwards? (%ld)"),
                     (long)frag->fr_offset);
    }

    frag->fr_type = rs_space;
}

/* We need to avoid having labels defined for certain directives/pseudo-ops
   since once the label is defined, it's in the symbol table for good.  TI
   syntax puts the symbol *before* the pseudo (which is kinda like MRI syntax,
   I guess, except I've never seen a definition of MRI syntax).

   Don't allow labels to start with '.'  */

int tic54x_start_label(char *label_start, int nul_char, int next_char) {
    char *rest;

    if (current_stag != NULL)
        return 0;

    if (next_char != ':') {
        if (*label_start == '.') {
            as_bad(_("Invalid label '%s'"), label_start);
            return 0;
        }
    }

    if (is_end_of_stmt(next_char))
        return 1;

    rest = input_line_pointer;
    if (nul_char == '"')
        ++rest;

    while (is_whitespace(next_char)) {
        next_char = *++rest;
    }

    if (next_char != '.')
        return 1;

    if ((strncasecmp(rest, ".tag", 4) == 0 && is_whitespace(rest[4])) ||
        (strncasecmp(rest, ".struct", 7) == 0 && is_whitespace(rest[7])) ||
        (strncasecmp(rest, ".union", 6) == 0 && is_whitespace(rest[6])) ||
        (strncasecmp(rest, ".macro", 6) == 0 && is_whitespace(rest[6])) ||
        (strncasecmp(rest, ".set", 4) == 0 && is_whitespace(rest[4])) ||
        (strncasecmp(rest, ".equ", 4) == 0 && is_whitespace(rest[4])))
        return 0;

    return 1;
}
