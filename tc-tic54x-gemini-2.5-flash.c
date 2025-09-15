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
  if (stream == NULL) {
    return;
  }

  fprintf (stream, _("C54x-specific command line options:\n"));
  fprintf (stream, _("-mfar-mode | -mf          Use extended addressing\n"));
  fprintf (stream, _("-mcpu=<CPU version>       Specify the CPU version\n"));
  fprintf (stream, _("-merrors-to-file <filename>\n"));
  fprintf (stream, _("-me <filename>            Redirect errors to a file\n"));
}

/* Output a single character (upper octet is zero).  */

static const int TIC54X_CHAR_EXPR_EMIT_PARAM = 2;

static void
tic54x_emit_char (char c)
{
  expressionS expn;

  expn.X_op = O_constant;
  expn.X_add_number = c;
  emit_expr (&expn, TIC54X_CHAR_EXPR_EMIT_PARAM);
}

/* Walk backwards in the frag chain.  */

static fragS *
frag_prev (fragS *frag, segT seg)
{
  segment_info_type *seginfo = seg_info(seg);
  if (seginfo == NULL) {
    return NULL;
  }

  if (seginfo->frchainP == NULL) {
    return NULL;
  }

  fragS *current_node;

  for (current_node = seginfo->frchainP->frch_root;
       current_node != NULL;
       current_node = current_node->fr_next)
  {
    if (current_node->fr_next == frag) {
      return current_node;
    }
  }

  return NULL;
}

static fragS *
bit_offset_frag (fragS *frag, segT seg)
{
  while (frag != NULL)
  {
    if (frag->fr_fix != 0 || frag->fr_opcode != NULL || frag->tc_frag_data != 0)
    {
      return frag;
    }
    frag = frag_prev (frag, seg);
  }
  return NULL;
}

/* Return the number of bits allocated in the most recent word, or zero if
   none. .field/.space/.bes may leave words partially allocated.  */

static int
frag_bit_offset (fragS *frag, segT seg)
{
  fragS *offset_frag = bit_offset_frag (frag, seg);

  if (offset_frag)
    {
      if (offset_frag->fr_opcode != NULL)
        {
          return -1;
        }
      else
        {
          return offset_frag->tc_frag_data;
        }
    }

  return 0;
}

/* Read an expression from a C string; returns a pointer past the end of the
   expression.  */

char *expression(char *current_pos, expressionS *expn);

static char *
parse_expression (char *str, expressionS *expn)
{
  if (str == NULL || expn == NULL) {
    return NULL;
  }

  char *new_pos = expression(str, expn);

  return new_pos;
}

/* .asg "character-string"|character-string, symbol

   .eval is the only pseudo-op allowed to perform arithmetic on substitution
   symbols.  all other use of symbols defined with .asg are currently
   unsupported.  */

static void
tic54x_asg (int x ATTRIBUTE_UNUSED)
{
  char *value_str = NULL;
  char *symbol_name = NULL;
  int current_char;
  int quoted = *(char *)input_line_pointer == '"';

  ILLEGAL_WITHIN_STRUCT ();

  if (quoted)
    {
      int len;
      value_str = demand_copy_C_string (&len);
      if (value_str == NULL)
        {
          as_bad (_("Memory allocation failed for string value."));
          goto cleanup;
        }
      current_char = *(char *)input_line_pointer;
    }
  else
    {
      const char *str_start = (char *)input_line_pointer;
      while ((current_char = *(char *)input_line_pointer) != ',')
	{
	  if (is_end_of_stmt (current_char))
	    break;
	  ++input_line_pointer;
	}
      size_t len = (char *)input_line_pointer - str_start;
      value_str = notes_memdup (str_start, len, len + 1);
      if (value_str == NULL)
        {
          as_bad (_("Memory allocation failed for string value."));
          goto cleanup;
        }
    }

  if (current_char != ',')
    {
      as_bad (_("Comma and symbol expected for '.asg STRING, SYMBOL'"));
      ignore_rest_of_line ();
      goto cleanup;
    }

  ++input_line_pointer;
  char *temp_name_ptr = NULL;
  int terminator_char = get_symbol_name (&temp_name_ptr);

  symbol_name = notes_strdup (temp_name_ptr);
  if (symbol_name == NULL)
    {
      as_bad (_("Memory allocation failed for symbol name."));
      goto cleanup;
    }

  (void) restore_line_pointer (terminator_char);

  if (!ISALPHA ((unsigned char)*symbol_name))
    {
      as_bad (_("symbols assigned with .asg must begin with a letter"));
      ignore_rest_of_line ();
      goto cleanup;
    }

  subsym_create_or_replace (symbol_name, value_str);

  demand_empty_rest_of_line ();

cleanup:
  notes_free (value_str);
  notes_free (symbol_name);
  return;
}

/* .eval expression, symbol
   There's something screwy about this.  The other assembler sometimes does and
   sometimes doesn't substitute symbols defined with .eval.
   We'll put the symbols into the subsym table as well as the normal symbol
   table, since that's what works best.  */

static void
tic54x_eval (int x ATTRIBUTE_UNUSED)
{
  char c;
  int value;
  char *p_name_from_input;
  symbolS *symbolP;
  char valuestr[32];
  char *value_str_duplicated;
  int quoted;

  ILLEGAL_WITHIN_STRUCT ();

  SKIP_WHITESPACE ();

  quoted = *input_line_pointer == '"';
  if (quoted)
    ++input_line_pointer;
  value = get_absolute_expression ();
  if (quoted)
    {
      if (*input_line_pointer != '"')
	{
	  as_bad (_("Unterminated string after absolute expression"));
	  ignore_rest_of_line ();
	  return;
	}
      ++input_line_pointer;
    }
  if (*input_line_pointer++ != ',')
    {
      as_bad (_("Comma and symbol expected for '.eval EXPR, SYMBOL'"));
      ignore_rest_of_line ();
      return;
    }
  c = get_symbol_name (&p_name_from_input);
  if (!ISALPHA (*p_name_from_input))
    {
      as_bad (_("symbols assigned with .eval must begin with a letter"));
      (void) restore_line_pointer (c);
      ignore_rest_of_line ();
      return;
    }
  char *name_duplicated = notes_strdup (p_name_from_input);
  (void) restore_line_pointer (c);

  symbolP = symbol_new (name_duplicated, absolute_section, &zero_address_frag, value);
  SF_SET_LOCAL (symbolP);
  symbol_table_insert (symbolP);

  snprintf (valuestr, sizeof(valuestr), "%d", value);
  value_str_duplicated = notes_strdup (valuestr);
  subsym_create_or_replace (name_duplicated, value_str_duplicated);

  demand_empty_rest_of_line ();
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

static void
tic54x_bss (void)
{
  char c;
  char *name = NULL;
  offsetT words = 0;
  int block = 0;
  int align = 0;

  segT current_seg = now_seg;
  subsegT current_subseg = now_subseg;

  ILLEGAL_WITHIN_STRUCT ();

  c = get_symbol_name (&name);
  if (c == '"')
    c = * ++ input_line_pointer;
  if (c != ',')
    {
      as_bad (_(".bss size argument missing\n"));
      ignore_rest_of_line ();
      return;
    }

  ++input_line_pointer;
  words = get_absolute_expression ();
  if (words < 0)
    {
      as_bad (_(".bss size %d < 0!"), (int) words);
      ignore_rest_of_line ();
      return;
    }

  if (*input_line_pointer == ',')
    {
      ++input_line_pointer;
      if (*input_line_pointer != ',')
	    block = get_absolute_expression ();

      if (*input_line_pointer == ',')
	    {
	      ++input_line_pointer;
	      align = get_absolute_expression ();
	    }
    }

  subseg_set (bss_section, 0);
  symbolS *symbolP = symbol_find_or_make (name);

  if (S_GET_SEGMENT (symbolP) == bss_section)
    symbol_get_frag (symbolP)->fr_symbol = NULL;

  symbol_set_frag (symbolP, frag_now);
  char *p = frag_var (rs_org, 1, 1, 0, symbolP, words * OCTETS_PER_BYTE, NULL);
  *p = 0;

  S_SET_SEGMENT (symbolP, bss_section);

  if (S_GET_STORAGE_CLASS (symbolP) != C_EXT)
    S_SET_STORAGE_CLASS (symbolP, C_STAT);

  if (align)
    {
      s_align_bytes (4);
      --input_line_pointer;
    }

  if (block)
    bss_section->flags |= SEC_TIC54X_BLOCK;

  subseg_set (current_seg, current_subseg);
  demand_empty_rest_of_line ();
}

static void
stag_add_field_symbols (struct stag *stag,
			const char *path,
			bfd_vma base_offset,
			symbolS *rootsym,
			const char *root_stag_name)
{
  char *prefix;
  struct stag_field *field = stag->field;

  prefix = concat (path, *path ? "." : "", (const char *) NULL);

  while (field != NULL)
    {
      char *field_full_name = concat (prefix, field->name, (const char *) NULL);

      if (rootsym == NULL)
	{
	  symbolS *sym;
	  sym = symbol_new (field_full_name, absolute_section, &zero_address_frag,
			    (field->stag ? field->offset
			     : base_offset + field->offset));
	  SF_SET_LOCAL (sym);
	  symbol_table_insert (sym);
	  /* `symbol_new` is assumed to copy `field_full_name`, so we free our allocated string. */
	  free (field_full_name);
	}
      else
	{
	  subsym_ent_t *ent = xmalloc (sizeof (*ent));

	  ent->u.s = concat (S_GET_NAME (rootsym), "+", root_stag_name,
			     field_full_name + strlen (S_GET_NAME (rootsym)),
			     (const char *) NULL);
	  ent->freekey = 1; /* Indicates `field_full_name` (key) is freed by the hash table. */
	  ent->freeval = 1; /* Indicates `ent` (value) is freed by the hash table.
	                       The hash table's freeing function for `ent` must also free `ent->u.s`. */
	  ent->isproc = 0;
	  ent->ismath = 0;
	  str_hash_insert (subsym_hash[0], field_full_name, ent, 0);
	  /* `field_full_name` is NOT freed here because `ent->freekey = 1` indicates ownership transfer. */
	}

      if (field->stag != NULL)
	stag_add_field_symbols (field->stag, field_full_name,
				field->offset,
				rootsym, root_stag_name);

      field = field->next;
    }
  free (prefix);
}

/* Keep track of stag fields so that when structures are nested we can add the
   complete dereferencing symbols to the symbol table.  */

static void
stag_add_field (struct stag *parent,
                const char *name,
                bfd_vma offset,
                struct stag *stag)
{
  /* Validate critical input pointers to prevent dereferencing NULL. */
  if (parent == NULL || name == NULL)
    {
      return;
    }

  struct stag_field *sfield = XCNEW (struct stag_field);
  /* If XCNEW (typically xcalloc) can return NULL, handle allocation failure.
     If it guarantees abort on OOM, this check is technically redundant at runtime
     but satisfies static analysis tools. */
  if (sfield == NULL)
    {
      return;
    }

  sfield->name = xstrdup (name);
  /* If xstrdup can return NULL (e.g., on OOM) without aborting,
     it's crucial to check its return value. If it fails, clean up the
     already allocated sfield and return to prevent memory leaks and inconsistent state. */
  if (sfield->name == NULL)
    {
      XCFREE (sfield); /* Assuming XCFREE is the counterpart to XCNEW */
      return;
    }

  sfield->offset = offset;
  sfield->bitfield_offset = parent->current_bitfield_offset;
  sfield->stag = stag;
  sfield->next = NULL; /* Explicitly initialize the next pointer for clarity and safety. */

  /* Append the new field to the parent's linked list.
     Using a pointer-to-pointer simplifies the logic, removing the special
     case for the first element. */
  struct stag_field **current_next_ptr = &parent->field;
  while (*current_next_ptr != NULL)
    {
      current_next_ptr = &(*current_next_ptr)->next;
    }
  *current_next_ptr = sfield;

  /* Use a named constant for the magic string ".fake" to improve maintainability. */
  static const char *const FAKE_PARENT_NAME_PREFIX = ".fake";
  if (startswith (parent->name, FAKE_PARENT_NAME_PREFIX))
    {
      symbolS *sym = symbol_new (name, absolute_section, &zero_address_frag,
                                 offset);
      /* Check if symbol_new returned a valid symbol.
         Similar to memory allocation, if this function can return NULL on failure,
         it should be handled. */
      if (sym != NULL)
        {
          SF_SET_LOCAL (sym);
          symbol_table_insert (sym);
        }
    }
}

/* [STAG] .struct       [OFFSET]
   Start defining structure offsets (symbols in absolute section).  */

static void
tic54x_struct (int is_union)
{
  int initial_expression_offset = 0;

  if (!current_stag)
    {
      stag_saved_seg = now_seg;
      stag_saved_subseg = now_subseg;
      subseg_set (absolute_section, 0);
    }
  else if (current_stag->current_bitfield_offset != 0)
    {
      ++abs_section_offset;
      current_stag->current_bitfield_offset = 0;
    }

  if (!is_union)
    {
      SKIP_WHITESPACE ();
      if (!is_end_of_stmt (*input_line_pointer))
        initial_expression_offset = get_absolute_expression ();
    }

  struct stag *new_stag_instance = XCNEW (struct stag);

  if (current_stag)
    {
      current_stag->inner = new_stag_instance;
      new_stag_instance->outer = current_stag;
      current_stag = new_stag_instance;
      if (initial_expression_offset)
        as_warn (_("Offset on nested structures is ignored"));
    }
  else
    {
      current_stag = new_stag_instance;
      abs_section_offset = initial_expression_offset;
    }
  current_stag->is_union = is_union;

  char *symbol_name = NULL;
  if (line_label == NULL)
    {
      static int struct_count = 0;
      if (xasprintf (&symbol_name, ".fake_stag%d", struct_count++) < 0)
        {
          return;
        }
    }
  else
    {
      symbol_name = xstrdup (S_GET_NAME (line_label));
      if (!symbol_name)
        {
          return;
        }
    }

  current_stag->sym = symbol_new (symbol_name,
                                  absolute_section,
                                  &zero_address_frag,
                                  abs_section_offset);
  free (symbol_name);

  current_stag->name = S_GET_NAME (current_stag->sym);
  SF_SET_LOCAL (current_stag->sym);
  if (current_stag->outer == NULL)
    symbol_table_insert (current_stag->sym);

  line_label = NULL;
}

/* [LABEL] .endstruct
   finish defining structure offsets; optional LABEL's value will be the size
   of the structure.  */

static void
tic54x_endstruct (int is_union)
{
  const char *type_str = is_union ? "union" : "struct";
  int calculated_size;
  const char *path;

  if (!current_stag || current_stag->is_union != is_union)
    {
      as_bad (_(".end%s without preceding .%s"), type_str, type_str);
      ignore_rest_of_line ();
      return;
    }

  path = startswith (current_stag->name, ".fake") ? "" : current_stag->name;

  if (current_stag->current_bitfield_offset)
    {
      ++abs_section_offset;
      current_stag->current_bitfield_offset = 0;
    }

  if (current_stag->is_union)
    calculated_size = current_stag->size;
  else
    calculated_size = abs_section_offset - S_GET_VALUE (current_stag->sym);

  if (line_label != NULL)
    {
      S_SET_VALUE (line_label, calculated_size);
      symbol_table_insert (line_label);
      line_label = NULL;
    }

  if (!current_stag->is_union)
    current_stag->size = calculated_size;

  if (current_stag->outer == NULL)
    {
      str_hash_insert (stag_hash, current_stag->name, current_stag, 0);
      stag_add_field_symbols (current_stag, path,
			      S_GET_VALUE (current_stag->sym),
			      NULL, NULL);
    }

  struct stag *closed_stag = current_stag;
  current_stag = current_stag->outer;

  if (current_stag != NULL)
    {
      stag_add_field (current_stag, closed_stag->name,
		      S_GET_VALUE (closed_stag->sym),
		      closed_stag);
    }
  else
    {
      subseg_set (stag_saved_seg, stag_saved_subseg);
    }
}

/* [LABEL]      .tag    STAG
   Reference a structure within a structure, as a sized field with an optional
   label.
   If used outside of a .struct/.endstruct, overlays the given structure
   format on the existing allocated space.  */

static void
tic54x_tag ()
{
  char *name;
  int c = get_symbol_name (&name);
  struct stag *stag = str_hash_find (stag_hash, name);

  if (!stag)
    {
      if (*name)
	as_bad (_("Unrecognized struct/union tag '%s'"), name);
      else
	as_bad (_(".tag requires a structure tag"));
      ignore_rest_of_line ();
      goto cleanup_and_return;
    }

  if (line_label == NULL)
    {
      as_bad (_("Label required for .tag"));
      ignore_rest_of_line ();
      goto cleanup_and_return;
    }

  char *label = xstrdup (S_GET_NAME (line_label));

  if (current_stag != NULL)
    {
      stag_add_field (current_stag, label,
                      abs_section_offset - S_GET_VALUE (current_stag->sym),
                      stag);
    }
  else
    {
      symbolS *sym = symbol_find (label);
      if (!sym)
	{
	  as_bad (_(".tag target '%s' undefined"), label);
	  ignore_rest_of_line ();
	  free (label);
	  goto cleanup_and_return;
	}
      stag_add_field_symbols (stag, S_GET_NAME (sym),
                              S_GET_VALUE (stag->sym), sym, stag->name);
    }

  free (label);

  if (current_stag != NULL && !current_stag->is_union)
    abs_section_offset += stag->size;

cleanup_and_return:
  (void) restore_line_pointer (c);
  demand_empty_rest_of_line ();
  line_label = NULL;
}

/* Handle all .byte, .char, .double, .field, .float, .half, .int, .long,
   .short, .string, .ubyte, .uchar, .uhalf, .uint, .ulong, .ushort, .uword,
   and .word.  */

static void
tic54x_struct_field (int type_char)
{
  unsigned int field_data_size_bytes = 0;
  int field_element_count_or_bit_length = 1;
  int next_bitfield_offset = 0;
  int needs_word_start_alignment = (current_stag->current_bitfield_offset != 0);
  int needs_longword_alignment = 0;

  SKIP_WHITESPACE ();
  if (!is_end_of_stmt (*input_line_pointer))
    field_element_count_or_bit_length = get_absolute_expression ();

  switch (type_char)
    {
    case 'b': case 'B': case 'c': case 'C':
    case 'h': case 'H': case 'i': case 'I':
    case 's': case 'S': case 'w': case 'W':
    case '*':
      field_data_size_bytes = 1;
      break;
    case 'f':
    case 'l':
    case 'L':
      needs_longword_alignment = 1;
      field_data_size_bytes = 2;
      break;
    case '.':
      {
	unsigned int bitfield_length = field_element_count_or_bit_length;

	if (bitfield_length < 1 || bitfield_length > 32)
	  {
	    as_bad (_(".field count '%d' out of range (1 <= X <= 32)"), bitfield_length);
	    ignore_rest_of_line ();
	    return;
	  }

	if (current_stag->current_bitfield_offset + bitfield_length > 16)
	  {
	    if (bitfield_length == 32)
	      {
		field_data_size_bytes = 2;
		field_element_count_or_bit_length = 1;
		next_bitfield_offset = 0;
	      }
	    else if (bitfield_length > 16)
	      {
		field_data_size_bytes = 1;
		field_element_count_or_bit_length = 1;
		next_bitfield_offset = bitfield_length - 16;
	      }
	    else
	      {
		next_bitfield_offset = bitfield_length;
	      }
	  }
	else
	  {
	    needs_word_start_alignment = 0;
	    next_bitfield_offset = current_stag->current_bitfield_offset + bitfield_length;
	  }
      }
      break;
    default:
      as_bad (_("Unrecognized field type '%c'"), type_char);
      ignore_rest_of_line ();
      return;
    }

  if (needs_word_start_alignment)
    {
      current_stag->current_bitfield_offset = 0;
      ++abs_section_offset;
    }
  if (needs_longword_alignment && (abs_section_offset & 0x1))
    ++abs_section_offset;

  if (line_label == NULL)
    {
      static int field_index_counter = 0;
      char fake_field_name_buffer[23];

      snprintf (fake_field_name_buffer, sizeof(fake_field_name_buffer),
		".fake_field%d", field_index_counter++);
      stag_add_field (current_stag, fake_field_name_buffer,
		      abs_section_offset - S_GET_VALUE (current_stag->sym),
		      NULL);
    }
  else
    {
      char *label_name = xstrdup (S_GET_NAME (line_label));
      stag_add_field (current_stag, label_name,
		      abs_section_offset - S_GET_VALUE (current_stag->sym),
		      NULL);
      free (label_name);
    }

  if (current_stag->is_union)
    {
      if (current_stag->size < (unsigned int)(field_data_size_bytes * field_element_count_or_bit_length))
	current_stag->size = field_data_size_bytes * field_element_count_or_bit_length;
    }
  else
    {
      abs_section_offset += field_data_size_bytes * field_element_count_or_bit_length;
      current_stag->current_bitfield_offset = next_bitfield_offset;
    }
  line_label = NULL;
}

/* Handle .byte, .word. .int, .long and all variants.  */

static void
tic54x_cons (int type)
{
  unsigned int c;
  int octets;
  const offsetT BYTE_POS_WARN_LIMIT = 0xFF;
  const offsetT BYTE_NEG_WARN_LIMIT = -0x100;
  const offsetT WORD_POS_WARN_LIMIT = 0xFFFF;
  const offsetT WORD_NEG_WARN_LIMIT = -0x10000;

  if (current_stag != NULL)
    {
      tic54x_struct_field (type);
      return;
    }

#ifdef md_flush_pending_output
  md_flush_pending_output ();
#endif

  generate_lineno_debug ();

  if (type == 'l' || type == 'L')
    {
      frag_align (2, 0, 2);
      if (line_label != NULL)
	{
	  symbol_set_frag (line_label, frag_now);
	  S_SET_VALUE (line_label, frag_now_fix ());
	}
    }

  switch (type)
    {
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

  while (true)
    {
      if (*input_line_pointer == '"')
	{
	  input_line_pointer++;
	  while (is_a_char (c = next_char_of_string ()))
	    tic54x_emit_char (c);
	  know (input_line_pointer[-1] == '\"');
	}
      else
	{
	  expressionS expn;

	  input_line_pointer = parse_expression (input_line_pointer, &expn);
	  if (expn.X_op == O_constant)
	    {
	      offsetT value = expn.X_add_number;
	      switch (octets)
		{
		case 1:
		  if (value > BYTE_POS_WARN_LIMIT || value < BYTE_NEG_WARN_LIMIT)
		    as_warn (_("Overflow in expression, truncated to 8 bits"));
		  break;
		case 2:
		  if (value > WORD_POS_WARN_LIMIT || value < WORD_NEG_WARN_LIMIT)
		    as_warn (_("Overflow in expression, truncated to 16 bits"));
		  break;
		}
	    }
	  if (expn.X_op != O_constant && octets < 2)
	    {
	      as_bad (_("Relocatable values require at least WORD storage"));
	      ignore_rest_of_line ();
	      return;
	    }

	  if (expn.X_op != O_constant
	      && amode == c_mode
	      && octets == 4)
	    {
	      amode = far_mode;
	      emitting_long = 1;
	      emit_expr (&expn, 4);
	      emitting_long = 0;
	      amode = c_mode;
	    }
	  else
	    {
	      emitting_long = (octets == 4);
	      emit_expr (&expn, (octets == 1) ? 2 : octets);
	      emitting_long = 0;
	    }
	}

      if (*input_line_pointer == ',')
	{
	  input_line_pointer++;
	}
      else
	{
	  break;
	}
    }

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
  char *name = NULL;
  int c;
  symbolS *symbolP;
  int keep_parsing = 1;

  if (type == 'r')
    as_warn (_("Use of .def/.ref is deprecated.  Use .global instead"));

  ILLEGAL_WITHIN_STRUCT ();

  do
    {
      c = get_symbol_name (&name);

      // Validate that a symbol name was successfully retrieved.
      // This prevents potential null pointer dereferences if get_symbol_name fails.
      if (name == NULL) {
          // A symbol name was expected but not found. This indicates an input error
          // or an unexpected end of input. Terminate parsing for reliability.
          keep_parsing = 0;
          break;
      }

      symbolP = symbol_find_or_make (name);
      // Validate that symbol creation/finding was successful.
      // If symbol_find_or_make can return NULL (e.g., due to memory allocation failure),
      // this check prevents further issues.
      if (symbolP == NULL) {
          // Free the symbol name if it was dynamically allocated, to prevent leaks.
          free(name);
          name = NULL;
          keep_parsing = 0;
          break;
      }

      // Adjust the input line pointer based on the character 'c' which followed the symbol name.
      // 'c' will then hold the actual delimiter character.
      c = restore_line_pointer (c);

      S_SET_STORAGE_CLASS (symbolP, C_EXT);

      // Assuming 'get_symbol_name' dynamically allocates memory for 'name'.
      // It must be freed here to prevent memory leaks, as 'symbol_find_or_make'
      // is expected to copy or otherwise take ownership of the string content.
      free(name);
      name = NULL; // Clear pointer after freeing to prevent use-after-free issues.

      // Determine if there are more symbols to parse in the list.
      if (c == ',')
	{
	  // If a comma is found, advance the input pointer past it to prepare for the next symbol.
	  input_line_pointer++;

	  // Check if an end-of-statement character immediately follows the comma.
	  // This handles cases like ".global sym1," where a trailing comma might signify the end.
	  if (is_end_of_stmt (*input_line_pointer))
	    {
	      // If it's an end-of-statement, stop parsing more symbols in this list.
	      keep_parsing = 0;
	    }
	  // Otherwise, 'keep_parsing' remains true, and the loop will continue to the next symbol.
	}
      else
	{
	  // If the character 'c' is not a comma, it means there are no more symbols
	  // expected in this comma-separated list.
	  keep_parsing = 0;
	}
    }
  while (keep_parsing);

  // Ensure that there are no unexpected characters remaining on the current line.
  demand_empty_rest_of_line ();
}

static void
free_subsym_ent (void *ent)
{
  if (ent == NULL) {
    return;
  }

  string_tuple_t *tuple = (string_tuple_t *)ent;
  subsym_ent_t *val = (subsym_ent_t *)tuple->value;

  if (val != NULL) {
    if (val->freekey) {
      free((void *)tuple->key);
    }
    if (val->freeval) {
      free(val->u.s);
    }
    free(val);
  }

  free(tuple);
}

static const int SUBSYM_HTAB_INITIAL_CAPACITY = 16;

static htab_t
subsym_htab_create (void)
{
  return htab_create_alloc (SUBSYM_HTAB_INITIAL_CAPACITY,
                            hash_string_tuple,
                            eq_string_tuple,
                            free_subsym_ent,
                            xcalloc,
                            free);
}

static void
free_local_label_ent (void *ent)
{
  if (ent == NULL) {
    return;
  }

  string_tuple_t *tuple = (string_tuple_t *)ent;

  free(tuple->key);
  free(tuple->value);
  free(tuple);
}

#define INITIAL_HTAB_CAPACITY 16

static htab_t
local_label_htab_create (void)
{
  return htab_create_alloc (INITIAL_HTAB_CAPACITY, hash_string_tuple, eq_string_tuple,
			    free_local_label_ent, xcalloc, free);
}

/* Reset all local labels.  */

static void
tic54x_clear_local_labels (int ignored ATTRIBUTE_UNUSED)
{
  htab_t current_htab = local_label_hash[macro_level];

  if (current_htab != NULL)
    {
      htab_empty (current_htab);
    }
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

static void
tic54x_sect (int arg)
{
  ILLEGAL_WITHIN_STRUCT ();

  tic54x_clear_local_labels (0);

  if (arg == 't')
    s_text (0);
  else if (arg == 'd')
    s_data (0);
  else
    {
      char *base_name = NULL;
      char *full_section_name = NULL;
      const char *flags = ",\"w\"\n";

      if (*input_line_pointer == '"')
	{
	  int len;
	  base_name = demand_copy_C_string (&len);
	  demand_empty_rest_of_line ();
	}
      else
	{
	  int restore_point_c;
	  restore_point_c = get_symbol_name (&base_name);
	  (void) restore_line_pointer (restore_point_c);
	  demand_empty_rest_of_line ();
	}

      full_section_name = concat (base_name, flags, NULL);
      free (base_name);

      input_scrub_insert_line (full_section_name);
      obj_coff_section (0);

      if (line_label != NULL)
	{
	  S_SET_SEGMENT (line_label, now_seg);
	  symbol_set_frag (line_label, frag_now);
	  S_SET_VALUE (line_label, frag_now_fix ());
	  if (S_GET_STORAGE_CLASS (line_label) != C_EXT)
	    S_SET_STORAGE_CLASS (line_label, C_LABEL);
	}
    }
}

/* [symbol] .space space_in_bits
   [symbol] .bes space_in_bits
   BES puts the symbol at the *last* word allocated

   cribbed from s_space.  */

static void
tic54x_space (int arg)
{
  expressionS expn;
  int bes = arg;
  symbolS *label = line_label; /* Store initial label for use in all paths */

  ILLEGAL_WITHIN_STRUCT ();

#ifdef md_flush_pending_output
  md_flush_pending_output ();
#endif

  /* Read the bit count.  */
  expression (&expn);

  /* Some expressions are unresolvable until later in the assembly pass;
     postpone until relaxation/fixup. We also postpone if a previous
     partial allocation has not been completed yet.  */
  if (expn.X_op != O_constant || frag_bit_offset (frag_now, now_seg) == -1)
    {
      struct bit_info *bi = XNEW (struct bit_info);
      char *p_deferred_frag = NULL;

      bi->seg = now_seg;
      bi->type = bes;
      bi->sym = label;

      p_deferred_frag = frag_var (rs_machine_dependent, 65536 * 2, 1, 0,
                                  make_expr_symbol (&expn), 0, (char *) bi);
      if (p_deferred_frag)
        *p_deferred_frag = 0;

      demand_empty_rest_of_line ();
      return;
    }

  long total_bits_requested = expn.X_add_number;
  int bits_per_byte = (OCTETS_PER_BYTE * 8);
  int current_frag_bit_offset = frag_now->tc_frag_data;

  /* Reduce the required size by any bit offsets currently left over
     from a previous .space/.bes/.field directive.  */
  if (current_frag_bit_offset > 0 && current_frag_bit_offset < bits_per_byte)
    {
      int spare_bits_in_current_word = bits_per_byte - current_frag_bit_offset;

      if (spare_bits_in_current_word >= total_bits_requested)
        {
          /* Don't have to do anything; sufficient bits have already been
             allocated; just point the label to the right place.  */
          if (label != NULL)
            {
              symbol_set_frag (label, frag_now);
              S_SET_VALUE (label, frag_now_fix () - 1);
            }
          frag_now->tc_frag_data += total_bits_requested;
          demand_empty_rest_of_line ();
          return;
        }

      total_bits_requested -= spare_bits_in_current_word;
      /* Set the label to point to the first word allocated, which in this
         case is the previous word, which was only partially filled.  */
      if (!bes && label != NULL)
        {
          symbol_set_frag (label, frag_now);
          S_SET_VALUE (label, frag_now_fix () - 1);
          label = NULL; /* Label consumed, prevent re-assignment later */
        }
    }

  /* Convert remaining bits to words/octets, rounding up.  */
  long words_to_allocate = (total_bits_requested + bits_per_byte - 1) / bits_per_byte;
  int final_bit_offset_in_word = total_bits_requested % bits_per_byte;
  long octets_to_allocate = words_to_allocate * OCTETS_PER_BYTE;

  if (octets_to_allocate <= 0)
    {
      as_warn (_(".space/.bes repeat count is zero or negative, ignored"));
      demand_empty_rest_of_line ();
      return;
    }

  /* If we are in the absolute section, just bump the offset.  */
  if (now_seg == absolute_section)
    {
      abs_section_offset += words_to_allocate;
      if (bes && label != NULL)
        S_SET_VALUE (label, abs_section_offset - 1);
      frag_now->tc_frag_data = final_bit_offset_in_word;
      demand_empty_rest_of_line ();
      return;
    }

  char *p_allocated_frag = NULL;
  if (!need_pass_2)
    p_allocated_frag = frag_var (rs_fill, 1, 1, 0, NULL, octets_to_allocate, NULL);

  /* Make note of how many bits of this word we've allocated so far.  */
  frag_now->tc_frag_data = final_bit_offset_in_word;

  /* .bes puts label at *last* word allocated.  */
  if (bes && label != NULL)
    {
      symbol_set_frag (label, frag_now);
      S_SET_VALUE (label, frag_now_fix () - 1);
    }

  if (p_allocated_frag)
    *p_allocated_frag = 0;

  demand_empty_rest_of_line ();
}

/* [symbol] .usect "section-name", size-in-words
		   [, [blocking-flag] [, alignment-flag]]

   Uninitialized section.
   Non-zero blocking means that if the section would cross a page (128-word)
   boundary, it will be page-aligned.
   Non-zero alignment aligns on a longword boundary.

   Has no effect on the current section.  */

static void
tic54x_usect (int x ATTRIBUTE_UNUSED)
{
  segT current_seg;
  subsegT current_subseg;
  char *section_name_ptr;
  char *name;
  int size = 0;
  int blocking_flag = 0;
  int alignment_flag = 0;
  segT new_seg;
  flagword flags;
  char *frag_data_ptr;

  ILLEGAL_WITHIN_STRUCT ();

  current_seg = now_seg;
  current_subseg = now_subseg;

  char terminator_char = get_symbol_name (&section_name_ptr);
  name = xstrdup (section_name_ptr);
  terminator_char = restore_line_pointer (terminator_char);

  if (terminator_char != ',')
    {
      as_bad (_("Missing size argument"));
      ignore_rest_of_line ();
      return;
    }
  ++input_line_pointer;
  size = get_absolute_expression ();

  if (*input_line_pointer == ',')
    {
      ++input_line_pointer;
      if (*input_line_pointer != ',')
        {
          blocking_flag = get_absolute_expression ();
        }
    }

  if (*input_line_pointer == ',')
    {
      ++input_line_pointer;
      alignment_flag = get_absolute_expression ();
    }

  new_seg = subseg_new (name, 0);
  flags = bfd_section_flags (new_seg) | SEC_ALLOC;

  if (alignment_flag)
    {
      s_align_bytes (4);
      --input_line_pointer;
    }

  if (line_label != NULL)
    {
      S_SET_SEGMENT (line_label, new_seg);
      symbol_set_frag (line_label, frag_now);
      S_SET_VALUE (line_label, frag_now_fix ());
      if (S_GET_STORAGE_CLASS (line_label) != C_EXT)
        S_SET_STORAGE_CLASS (line_label, C_LABEL);
    }

  seg_info (new_seg)->bss = 1;

  frag_data_ptr = frag_var (rs_fill, 1, 1, 0, line_label, (long)size * OCTETS_PER_BYTE, NULL);
  *frag_data_ptr = 0;

  if (blocking_flag)
    {
      flags |= SEC_TIC54X_BLOCK;
    }

  if (!bfd_set_section_flags (new_seg, flags))
    {
      as_warn (_("Error setting flags for \"%s\": %s"), name,
               bfd_errmsg (bfd_get_error ()));
    }

  subseg_set (current_seg, current_subseg);
  demand_empty_rest_of_line ();
}

static enum cpu_version
lookup_version (const char *ver)
{
  enum cpu_version version = VNONE;

  if (ver == NULL)
    {
      return VNONE;
    }

  size_t len = strlen(ver);

  if (len < 2 || ver[0] != '5' || ver[1] != '4')
    {
      return VNONE;
    }

  switch (len)
    {
    case 3:
      switch (ver[2])
        {
        case '1':
        case '2':
        case '3':
        case '5':
        case '8':
        case '9':
          version = (enum cpu_version)(ver[2] - '0');
          break;
        default:
          break;
        }
      break;

    case 5:
      if (TOUPPER((unsigned char)ver[3]) == 'L' &&
          TOUPPER((unsigned char)ver[4]) == 'P')
        {
          switch (ver[2])
            {
            case '5':
            case '6':
              version = (enum cpu_version)(ver[2] - '0' + 10);
              break;
            default:
              break;
            }
        }
      break;

    default:
      break;
    }

  return version;
}

static void
set_cpu (enum cpu_version version)
{
  cpu = version;
  if (version == V545LP || version == V546LP)
    {
      symbolS *symbolP = symbol_new ("__allow_lp", absolute_section,
				     &zero_address_frag, 1);
      if (symbolP != NULL)
        {
          SF_SET_LOCAL (symbolP);
          symbol_table_insert (symbolP);
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

static void
tic54x_version (int x ATTRIBUTE_UNUSED)
{
  enum cpu_version version = VNONE;
  enum cpu_version old_version = cpu;
  int saved_char;
  char *version_str_start;
  char *null_term_pos;

  ILLEGAL_WITHIN_STRUCT ();

  SKIP_WHITESPACE ();
  version_str_start = input_line_pointer;

  while (!is_end_of_stmt (*input_line_pointer))
    ++input_line_pointer;

  null_term_pos = input_line_pointer;

  saved_char = *null_term_pos;
  *null_term_pos = 0;

  version = lookup_version (version_str_start);

  *null_term_pos = saved_char;

  if (cpu != VNONE && cpu != version)
    {
      as_warn (_("CPU version has already been set"));
    }

  if (version == VNONE)
    {
      as_bad (_("Unrecognized version '%s'"), version_str_start);
      ignore_rest_of_line ();
      return;
    }
  else if (assembly_begun && version != old_version)
    {
      as_bad (_("Changing of CPU version on the fly not supported"));
      ignore_rest_of_line ();
      return;
    }

  set_cpu (version);

  demand_empty_rest_of_line ();
}

/* 'f' = float, 'x' = xfloat, 'd' = double, 'l' = ldouble.  */

static void
tic54x_float_cons (int type)
{
  const int LONG_WORD_ALIGNMENT_WORDS = 2;
  const int ALIGNMENT_OFFSET = 0;
  const int MAX_PADDING_WORDS = LONG_WORD_ALIGNMENT_WORDS;

  if (current_stag != 0)
    {
      tic54x_struct_field ('f');
    }

#ifdef md_flush_pending_output
  md_flush_pending_output ();
#endif

  if (type != 'x')
    {
      frag_align (LONG_WORD_ALIGNMENT_WORDS, ALIGNMENT_OFFSET, MAX_PADDING_WORDS);

      if (line_label != NULL)
        {
          symbol_set_frag (line_label, frag_now);
          S_SET_VALUE (line_label, frag_now_fix ());
        }
    }

  float_cons ('f');
}

/* The argument is capitalized if it should be zero-terminated
   's' is normal string with upper 8-bits zero-filled, 'p' is packed.
   Code copied from stringer, and slightly modified so that strings are packed
   and encoded into the correct octets.  */

#include <stdbool.h>

#define NO_PENDING_CHAR -1

static void
tic54x_append_string_char (unsigned int c, bool packed, int* pending_packed_char)
{
  if (!packed)
    {
      FRAG_APPEND_1_CHAR (c);
      FRAG_APPEND_1_CHAR (0);
    }
  else
    {
      if (*pending_packed_char == NO_PENDING_CHAR)
        {
          *pending_packed_char = c;
        }
      else
        {
          FRAG_APPEND_1_CHAR (c);
          FRAG_APPEND_1_CHAR (*pending_packed_char);
          *pending_packed_char = NO_PENDING_CHAR;
        }
    }
}

static void
tic54x_pad_string_block_end (bool packed, int* pending_packed_char, bool append_zero)
{
  if (packed && *pending_packed_char != NO_PENDING_CHAR)
    {
      FRAG_APPEND_1_CHAR (0);
      FRAG_APPEND_1_CHAR (*pending_packed_char);
      *pending_packed_char = NO_PENDING_CHAR;
    }
  else if (append_zero)
    {
      FRAG_APPEND_1_CHAR (0);
      FRAG_APPEND_1_CHAR (0);
    }
}


static void
tic54x_stringer (int type)
{
  const bool append_zero = (type == 'S' || type == 'P');
  const bool packed = (type == 'p' || type == 'P');
  int pending_packed_char = NO_PENDING_CHAR;

  if (current_stag != NULL)
    {
      tic54x_struct_field ('*');
      return;
    }

#ifdef md_flush_pending_output
  md_flush_pending_output ();
#endif

  unsigned int separator_or_terminator;
  do
    {
      SKIP_WHITESPACE ();

      switch (*input_line_pointer)
        {
        default:
          {
            unsigned short value = get_absolute_expression ();
            FRAG_APPEND_1_CHAR (value & 0xFF);
            FRAG_APPEND_1_CHAR ((value >> 8) & 0xFF);
            break;
          }
        case '\"':
          {
            ++input_line_pointer;
            unsigned int current_char_from_string;

            while (is_a_char (current_char_from_string = next_char_of_string ()))
              {
                tic54x_append_string_char (current_char_from_string, packed, &pending_packed_char);
              }

            tic54x_pad_string_block_end (packed, &pending_packed_char, append_zero);
            
            know (input_line_pointer[-1] == '\"');
            break;
          }
        }

      SKIP_WHITESPACE ();
      separator_or_terminator = *input_line_pointer;

      if (!is_end_of_stmt (separator_or_terminator))
        {
          ++input_line_pointer;
        }
    }
  while (separator_or_terminator == ',');

  demand_empty_rest_of_line ();
}

static void
tic54x_p2align (int arg)
{
  (void)arg;
  as_bad (_("p2align not supported on this target"));
}

static void
tic54x_align_words (int arg)
{
  const int ARG_EVEN_WARNING_VALUE = 2;
  const int ARG_STRUCT_SPECIAL_VALUE = 128;
  const int WORDS_TO_BYTES_SHIFT = 1;

  if (current_stag != NULL && arg == ARG_STRUCT_SPECIAL_VALUE)
    {
      if (current_stag->current_bitfield_offset != 0)
        {
          current_stag->current_bitfield_offset = 0;
          ++abs_section_offset;
        }
      demand_empty_rest_of_line ();
      return;
    }

  ILLEGAL_WITHIN_STRUCT ();

  int alignment_value = arg;

  if (!is_end_of_stmt (*input_line_pointer))
    {
      if (arg == ARG_EVEN_WARNING_VALUE)
        {
          as_warn (_("Argument to .even ignored"));
        }
      else
        {
          alignment_value = get_absolute_expression ();
        }
    }

  s_align_bytes (alignment_value << WORDS_TO_BYTES_SHIFT);
}

/* Initialize multiple-bit fields within a single word of memory.  */

static void
tic54x_field(int ignore ATTRIBUTE_UNUSED)
{
  expressionS expn;
  int field_size = 16;
  valueT field_value;
  symbolS *current_label = line_label;

  if (current_stag != NULL)
    {
      tic54x_struct_field('.');
      return;
    }

  input_line_pointer = parse_expression(input_line_pointer, &expn);

  if (*input_line_pointer == ',')
    {
      ++input_line_pointer;
      field_size = get_absolute_expression();
      if (field_size < 1 || field_size > 32)
	{
	  as_bad(_("Invalid field size, must be from 1 to 32"));
	  ignore_rest_of_line();
	  return;
	}
    }

  if (expn.X_op != O_constant)
    {
      if (field_size != 16)
	{
	  as_bad(_("field size must be 16 when value is relocatable"));
	  ignore_rest_of_line();
	  return;
	}
      frag_now->tc_frag_data = 0;
      emit_expr(&expn, 2);
    }
  else
    {
      const unsigned long fmask = (field_size == 32) ? 0xFFFFFFFF : (1ul << field_size) - 1;

      field_value = expn.X_add_number;
      expn.X_add_number &= fmask;

      if (field_value != (valueT)expn.X_add_number)
	as_warn(_("field value truncated"));

      field_value = expn.X_add_number;

      /* For sizes 16-32, process in 16-bit chunks. */
      while (field_size >= 16)
	{
	  char *p = frag_more(2);
	  frag_now->tc_frag_data = 0; /* Reset partial word count */
	  md_number_to_chars(p, (field_value >> (field_size - 16)) & 0xFFFF, 2);
	  field_size -= 16;
	}

      /* Handle remaining bits (0-15). */
      if (field_size > 0)
	{
	  char *p_frag_data;
	  fragS *target_frag;
	  int current_bit_offset = frag_bit_offset(frag_now, now_seg);

	  if (current_bit_offset == -1) /* New bit field or unknown offset */
	    {
	      struct bit_info *bi = XNEW(struct bit_info);
	      expressionS size_exp;

	      size_exp.X_op = O_constant;
	      size_exp.X_add_number = field_size;
	      bi->seg = now_seg;
	      bi->type = TYPE_FIELD;
	      bi->value = field_value;
	      frag_var(rs_machine_dependent, 4, 1, 0,
		       make_expr_symbol(&size_exp), 0, (char *)bi);
	    }
	  else
	    {
	      target_frag = bit_offset_frag(frag_now, now_seg);

	      if (target_frag == NULL || current_bit_offset == 0 || current_bit_offset + field_size > 16)
		{
		  /* Align a new field: either no existing partial word,
		     or the new field would span beyond the current word. */
		  p_frag_data = frag_more(2);
		  frag_now->tc_frag_data = 0;
		  target_frag = frag_now;
		}
	      else
		{
		  /* Put the new value entirely within the existing partial word. */
		  p_frag_data = target_frag->fr_literal;
		  if (current_label != NULL)
		    {
		      symbol_set_frag(current_label, target_frag);
		      S_SET_VALUE(current_label, frag_now_fix() - 1);
		      current_label = NULL;
		    }
		}

	      /* Shift the value to its position within the 16-bit word. */
	      field_value <<= (16 - target_frag->tc_frag_data - field_size);

	      /* OR in existing value if there's an active partial word. */
	      if (target_frag->tc_frag_data)
		field_value |= (((uint16_t)p_frag_data[1] << 8) | p_frag_data[0]);

	      md_number_to_chars(p_frag_data, field_value, 2);
	      target_frag->tc_frag_data += field_size;

	      if (target_frag->tc_frag_data == 16)
		target_frag->tc_frag_data = 0; /* Word is full */
	    }
	}
    }

  demand_empty_rest_of_line();
}

/* Ideally, we want to check SEC_LOAD and SEC_HAS_CONTENTS, but those aren't
   available yet.  seg_info ()->bss is the next best thing.  */

static int
tic54x_initialized_section (segT seg)
{
  const struct seg_info *info = seg_info (seg);
  if (info == NULL)
    {
      return 0;
    }
  return !info->bss;
}

/* .clink ["section name"]

   Marks the section as conditionally linked (link only if contents are
   referenced elsewhere.
   Without a name, refers to the current initialized section.
   Name is required for uninitialized sections.  */

static void
tic54x_clink (int ignored ATTRIBUTE_UNUSED)
{
  segT seg = now_seg;
  char *name_to_free = NULL;

  ILLEGAL_WITHIN_STRUCT ();

  if (*input_line_pointer == '\"')
    {
      char *section_name_start = ++input_line_pointer;

      while (is_a_char (next_char_of_string ()))
	;

      know (input_line_pointer[-1] == '\"');
      input_line_pointer[-1] = 0;

      name_to_free = xstrdup (section_name_start);
      if (name_to_free == NULL)
        {
          as_bad (_("Memory allocation failed for section name '%s'"), section_name_start);
          ignore_rest_of_line ();
          goto cleanup;
        }

      seg = bfd_get_section_by_name (stdoutput, name_to_free);
      if (seg == NULL)
	{
	  as_bad (_("Unrecognized section '%s'"), name_to_free);
	  ignore_rest_of_line ();
	  goto cleanup;
	}
    }
  else
    {
      if (!tic54x_initialized_section (seg))
	{
	  as_bad (_("Current section is uninitialized, "
		    "section name required for .clink"));
	  ignore_rest_of_line ();
	  goto cleanup;
	}
    }

  seg->flags |= SEC_TIC54X_CLINK;

  demand_empty_rest_of_line ();

cleanup:
  free (name_to_free);
}

/* Change the default include directory to be the current source file's
   directory.  */

static void
tic54x_set_default_include (void)
{
  unsigned dummy_lineno;
  const char *current_file_path = as_where(&dummy_lineno);
  const char *last_slash = strrchr(current_file_path, '/');
  
  if (last_slash != NULL)
    {
      size_t dir_len = last_slash - current_file_path;
      if (dir_len > include_dir_maxlen)
	include_dir_maxlen = dir_len;
      
      char *new_include_dir = notes_memdup(current_file_path, dir_len, dir_len + 1);
      
      if (new_include_dir != NULL)
        {
          include_dirs[0] = new_include_dir;
        }
      else
        {
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

static void
tic54x_include (int ignored ATTRIBUTE_UNUSED)
{
  const char *newblock_str = " .newblock\n";
  char *filename = NULL;
  char *input_for_insertion = NULL;
  int len; /* Retained to match demand_copy_C_string signature, though value is unused. */

  ILLEGAL_WITHIN_STRUCT ();
  SKIP_WHITESPACE ();

  char *filename_start_ptr = input_line_pointer;

  if (*input_line_pointer == '"')
    {
      /* If the filename is a quoted C string, demand_copy_C_string handles extraction and allocation.
         It advances input_line_pointer past the string. */
      filename = demand_copy_C_string (&len);
      demand_empty_rest_of_line ();
    }
  else
    {
      /* For unquoted filenames, find the end of the statement. */
      while (!is_end_of_stmt (*input_line_pointer))
	    ++input_line_pointer;

      /* Calculate length and use xstrndup to copy the filename.
         This avoids temporarily modifying the input buffer, improving robustness.
         Assumes xstrndup exists and exits on allocation failure. */
      size_t filename_len = input_line_pointer - filename_start_ptr;
      filename = xstrndup (filename_start_ptr, filename_len);
      demand_empty_rest_of_line ();
    }

  /* Construct the string to be inserted into the input stream.
     concat returns a newly allocated string. The contents of 'filename' are copied by concat.
     Assumes concat exists and exits on allocation failure. */
  input_for_insertion = concat ("\"", filename, "\"\n", newblock_str, (char *) NULL);

  /* Insert the constructed line into the input stream.
     Assumption: input_scrub_insert_line takes ownership of 'input_for_insertion'
     and is responsible for freeing it. */
  input_scrub_insert_line (input_for_insertion);

  /* Free the filename string, as concat has already copied its contents.
     This prevents a memory leak from demand_copy_C_string or xstrndup. */
  free (filename);

  tic54x_clear_local_labels (0);
  tic54x_set_default_include ();
  s_include (0);
}

static void
tic54x_message (int type)
{
  char *msg_allocated = NULL;
  char c;
  int len;

  ILLEGAL_WITHIN_STRUCT ();

  if (*input_line_pointer == '"')
    {
      msg_allocated = demand_copy_C_string (&len);
    }
  else
    {
      char *start_of_msg_segment = input_line_pointer;
      while (!is_end_of_stmt (*input_line_pointer))
	++input_line_pointer;

      c = *input_line_pointer;
      *input_line_pointer = '\0';
      msg_allocated = xstrdup (start_of_msg_segment);
      *input_line_pointer = c;
    }

  switch (type)
    {
    case 'm':
      as_tsktsk ("%s", msg_allocated);
      break;
    case 'w':
      as_warn ("%s", msg_allocated);
      break;
    case 'e':
      as_bad ("%s", msg_allocated);
      break;
    }

  demand_empty_rest_of_line ();

  if (msg_allocated != NULL)
    {
      free (msg_allocated);
    }
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
  char *name = NULL;
  symbolS *symbolP = NULL;
  int initial_parser_state;

  ILLEGAL_WITHIN_STRUCT ();

  initial_parser_state = get_symbol_name (&name);

  symbolP = colon (name);
  if (symbolP == NULL)
    {
      goto cleanup;
    }

  S_SET_STORAGE_CLASS (symbolP, C_STATLAB);

  (void) restore_line_pointer (initial_parser_state);
  (void) demand_empty_rest_of_line ();

cleanup:
  if (name != NULL)
    {
      free (name);
    }
}

/* .mmregs
   Install all memory-mapped register names into the symbol table as
   absolute local symbols.  */

static void
tic54x_register_mmregs (int ignored ATTRIBUTE_UNUSED)
{
  const tic54x_symbol *sym;

  ILLEGAL_WITHIN_STRUCT ();

  if (tic54x_mmregs == NULL) {
    // Using fprintf to stderr as a generic error logging mechanism.
    // In a real project, this would be replaced with a project-specific logging function.
    fprintf(stderr, "ERROR: tic54x_mmregs array is NULL. Cannot register symbols.\n");
    return;
  }

  for (sym = tic54x_mmregs; sym->name; sym++)
    {
      symbolS *symbolP = symbol_new (sym->name, absolute_section,
				     &zero_address_frag, sym->value);
      
      if (symbolP == NULL) {
        // Log the error and return immediately to prevent further operations
        // on a potentially compromised state, mimicking the original behavior
        // of aborting implicitly (via crash) but doing so gracefully.
        fprintf(stderr, "ERROR: Failed to create symbol for '%s'. Aborting symbol registration.\n",
                sym->name ? sym->name : "UNKNOWN");
        return;
      }

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
  int effective_count = count;
  if (!is_end_of_stmt (*input_line_pointer))
    {
      effective_count = get_absolute_expression ();
    }

  if (effective_count < 0)
    {
      effective_count = 0;
    }

  do_repeat ((size_t) effective_count, "LOOP", "ENDLOOP", NULL);
}

/* Normally, endloop gets eaten by the preceding loop.  */

static void
tic54x_endloop (int ignore __attribute__((unused)))
{
  as_bad (_("ENDLOOP without corresponding LOOP"));
  ignore_rest_of_line ();
}

/* .break [condition].  */

static void
tic54x_break (void)
{
  ILLEGAL_WITHIN_STRUCT ();

  SKIP_WHITESPACE ();

  if (is_end_of_stmt (*input_line_pointer) || get_absolute_expression ())
    {
      end_repeat (substitution_line ? 1 : 0);
    }
}

static void
set_address_mode (int mode)
{
  amode = mode;

  if (mode == far_mode)
    {
      symbolS *new_symbol = symbol_new ("__allow_far", absolute_section,
                                         &zero_address_frag, 1);

      if (new_symbol != NULL)
        {
          SF_SET_LOCAL (new_symbol);
          symbol_table_insert (new_symbol);
        }
    }
}

static int address_mode_needs_set = 1;

static void
tic54x_address_mode (const int mode)
{
  if (assembly_begun && amode != (unsigned) mode)
    {
      as_bad (_("Mixing of normal and extended addressing not supported"));
      ignore_rest_of_line ();
      return;
    }
  if (mode == far_mode && cpu != VNONE && cpu != V548 && cpu != V549)
    {
      as_bad (_("Extended addressing not supported on the specified CPU"));
      ignore_rest_of_line ();
      return;
    }

  set_address_mode (mode);
  demand_empty_rest_of_line ();
}

/* .sblock "section"|section [,...,"section"|section]
   Designate initialized sections for blocking.  */

static void
tic54x_sblock (int ignore ATTRIBUTE_UNUSED)
{
  char *section_name_ptr = NULL;
  int current_char_after_name;

  ILLEGAL_WITHIN_STRUCT ();

  do
    {
      if (*input_line_pointer == '"')
	{
	  section_name_ptr = demand_copy_C_string (NULL);
	}
      else
	{
	  char *name_buffer;
	  current_char_after_name = get_symbol_name (&name_buffer);
	  section_name_ptr = xstrdup (name_buffer);
	  (void) restore_line_pointer (current_char_after_name);
	}

      segT seg = bfd_get_section_by_name (stdoutput, section_name_ptr);
      if (seg == NULL)
	{
	  as_bad (_("Unrecognized section '%s'"), section_name_ptr);
	  ignore_rest_of_line ();
	  goto cleanup;
	}
      else if (!tic54x_initialized_section (seg))
	{
	  as_bad (_(".sblock may be used for initialized sections only"));
	  ignore_rest_of_line ();
	  goto cleanup;
	}

      seg->flags |= SEC_TIC54X_BLOCK;

      free (section_name_ptr);
      section_name_ptr = NULL;

      current_char_after_name = *input_line_pointer;

      if (is_end_of_stmt (current_char_after_name))
	{
	  break;
	}
      else if (current_char_after_name == ',')
	{
	  ++input_line_pointer;
	}
      else
	{
	  as_bad (_("Expected ',' or end of statement after section name, got '%c'"), current_char_after_name);
	  ignore_rest_of_line ();
	  break;
	}
    }
  while (1);

  demand_empty_rest_of_line ();
  return;

cleanup:
  free (section_name_ptr);
  return;
}

/* symbol .set value
   symbol .equ value

   value must be defined externals; no forward-referencing allowed
   symbols assigned with .set/.equ may not be redefined.  */

static void
tic54x_set (int ignore ATTRIBUTE_UNUSED)
{
  symbolS *symbolP;
  char *name;

  ILLEGAL_WITHIN_STRUCT ();

  if (!line_label)
    {
      as_bad (_("Symbol missing for .set/.equ"));
      ignore_rest_of_line ();
      return;
    }

  name = xstrdup (S_GET_NAME (line_label));
  line_label = NULL;

  // First, try to find an existing symbol.
  symbolP = symbol_find (name);

  // If not found, try to find a machine-dependent undefined symbol.
  if (symbolP == NULL)
    {
      symbolP = md_undefined_symbol (name);
    }

  // If still no symbol found, create a new one.
  if (symbolP == NULL)
    {
      symbolP = symbol_new (name, absolute_section, &zero_address_frag, 0);
      S_SET_STORAGE_CLASS (symbolP, C_STAT);
    }

  free (name); /* The name buffer is no longer needed after symbol lookup/creation. */

  S_SET_DATA_TYPE (symbolP, T_INT);
  S_SET_SEGMENT (symbolP, absolute_section);
  symbol_table_insert (symbolP);
  pseudo_set (symbolP);
  demand_empty_rest_of_line ();
}

/* .fclist
   .fcnolist
   List false conditional blocks.  */

static void
tic54x_fclist (int show)
{
  if (show)
  {
    listing &= ~LISTING_NOCOND;
  }
  else
  {
    listing |= LISTING_NOCOND;
  }
  demand_empty_rest_of_line ();
}

static void
tic54x_sslist (int show)
{
  listing_sslist = show;
}

/* .var SYM[,...,SYMN]
   Define a substitution string to be local to a macro.  */

static void
tic54x_var (int ignore ATTRIBUTE_UNUSED)
{
  char *name;
  int terminator_char;

  ILLEGAL_WITHIN_STRUCT ();

  if (macro_level == 0)
    {
      as_bad (_(".var may only be used within a macro definition"));
      ignore_rest_of_line ();
      return;
    }

  for (;;)
    {
      if (!ISALPHA (*input_line_pointer))
	{
	  as_bad (_("Substitution symbols must begin with a letter"));
	  ignore_rest_of_line ();
	  return;
	}

      terminator_char = get_symbol_name (&name);
      name = xstrdup (name);
      terminator_char = restore_line_pointer (terminator_char);

      subsym_ent_t *ent = xmalloc (sizeof (*ent));
      ent->u.s = (char *) "";
      ent->freekey = 1;
      ent->freeval = 0;
      ent->isproc = 0;
      ent->ismath = 0;
      str_hash_insert (subsym_hash[macro_level], name, ent, 0);

      if (terminator_char == ',')
	{
	  ++input_line_pointer;
	  if (is_end_of_stmt (*input_line_pointer))
	    {
	      /* This handles cases like ".var sym, \n" where the trailing comma
	         should still terminate the list of variables. */
	      break;
	    }
	}
      else
	{
	  /* Not a comma, so it's the end of the variable list (e.g., newline, semicolon). */
	  break;
	}
    }

  demand_empty_rest_of_line ();
}

/* .mlib <macro library filename>

   Macro libraries are archived (standard AR-format) text macro definitions
   Expand the file and include it.

   FIXME need to try the source file directory as well.  */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <unistd.h>
#include <ctype.h>

#ifndef ATTRIBUTE_UNUSED
#define ATTRIBUTE_UNUSED __attribute__((unused))
#endif

static void
tic54x_mlib (int ignore ATTRIBUTE_UNUSED)
{
  char *filename = NULL;
  char *path = NULL;
  int len = 0;
  bfd *abfd = NULL;
  bfd *mbfd = NULL;

  ILLEGAL_WITHIN_STRUCT ();

  /* Parse the filename.  */
  if (*input_line_pointer == '"')
    {
      filename = demand_copy_C_string (&len);
      if (filename == NULL)
        {
          return;
        }
    }
  else
    {
      SKIP_WHITESPACE ();
      char *start_ptr = input_line_pointer;
      while (!is_end_of_stmt (*input_line_pointer)
             && !is_whitespace (*input_line_pointer))
        {
          obstack_1grow (&notes, *input_line_pointer);
          ++input_line_pointer;
          ++len;
        }
      obstack_1grow (&notes, '\0');
      filename = obstack_finish (&notes);
      if (filename == NULL) {
          as_bad (_("Memory allocation failed for filename."));
          return;
      }
    }
  demand_empty_rest_of_line ();

  tic54x_set_default_include ();

  path = notes_alloc (len + include_dir_maxlen + 2);
  if (path == NULL) {
      as_bad (_("Memory allocation failed for path."));
      return;
  }

  FILE *try_file = search_and_open (filename, path);
  if (try_file)
    fclose (try_file);

  register_dependency (path);

  /* Expand all archive entries to temporary files and include them.  */
  abfd = bfd_openr (path, NULL);
  if (!abfd)
    {
      as_bad (_("can't open macro library file '%s' for reading: %s"),
	      path, bfd_errmsg (bfd_get_error ()));
      ignore_rest_of_line ();
      goto cleanup;
    }
  if (!bfd_check_format (abfd, bfd_archive))
    {
      as_bad (_("File '%s' not in macro archive format"), path);
      ignore_rest_of_line ();
      goto cleanup;
    }

  for (mbfd = bfd_openr_next_archived_file (abfd, NULL);
       mbfd != NULL; mbfd = bfd_openr_next_archived_file (abfd, mbfd))
    {
      bfd_size_type member_size = bfd_get_size (mbfd);
      char *buf = NULL;
      FILE *ftmp = NULL;
      char fname_template[256] = "/tmp/tic54x_mlib_XXXXXX";
      int fd = -1;
      bfd_size_type actual_read_size = 0;

      if (member_size == 0) {
          buf = XNEWVEC (char, 1);
          if (buf == NULL) {
              as_bad(_("Memory allocation failed for empty archive member."));
              goto member_cleanup;
          }
      } else {
          buf = XNEWVEC (char, member_size);
          if (buf == NULL) {
              as_bad(_("Memory allocation failed for archive member."));
              goto member_cleanup;
          }
      }

      fd = mkstemp(fname_template);
      if (fd == -1) {
          as_bad(_("Error creating temporary file: %s"), strerror(errno));
          goto member_cleanup;
      }

      ftmp = fdopen(fd, "w+b");
      if (ftmp == NULL) {
          as_bad(_("Error opening temporary file for writing: %s"), strerror(errno));
          close(fd);
          remove(fname_template);
          goto member_cleanup;
      }

      if (member_size > 0) {
          actual_read_size = bfd_read (buf, member_size, mbfd);
          if (actual_read_size == (bfd_size_type) -1) {
              as_bad(_("Error reading archive member: %s"), bfd_errmsg(bfd_get_error()));
              goto close_ftmp_and_remove_fname;
          }
      }

      if (actual_read_size > 0) {
          if (fwrite (buf, 1, actual_read_size, ftmp) != actual_read_size) {
              as_bad(_("Error writing to temporary file: %s"), strerror(errno));
              goto close_ftmp_and_remove_fname;
          }
      }

      if (actual_read_size == 0 || (actual_read_size > 0 && buf[actual_read_size - 1] != '\n')) {
          if (fwrite ("\n", 1, 1, ftmp) != 1) {
              as_bad(_("Error writing newline to temporary file: %s"), strerror(errno));
              goto close_ftmp_and_remove_fname;
          }
      }

      if (fflush(ftmp) != 0) {
          as_bad(_("Error flushing temporary file: %s"), strerror(errno));
          goto close_ftmp_and_remove_fname;
      }

    close_ftmp_and_remove_fname:
      if (fclose (ftmp) != 0) {
          as_bad(_("Error closing temporary file '%s': %s"), fname_template, strerror(errno));
      }
      ftmp = NULL;

      free (buf);
      buf = NULL;

      input_scrub_insert_file (fname_template);

      if (remove (fname_template) != 0) {
          as_bad(_("Error removing temporary file '%s': %s"), fname_template, strerror(errno));
      }
      continue;

    member_cleanup:
      if (buf != NULL) {
          free(buf);
          buf = NULL;
      }
      if (ftmp != NULL) {
          fclose(ftmp);
          ftmp = NULL;
      } else if (fd != -1) {
          close(fd);
      }
      if (fd != -1) {
          remove(fname_template);
      }
    }

  cleanup:
  if (abfd != NULL)
    bfd_close (abfd);
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
      {
	char *endptr;
	long version_long;

	errno = 0;
	version_long = strtol(arg, &endptr, 10);

	if (endptr == arg || *endptr != '\0' || errno == ERANGE)
	  {
	    as_fatal (_("Bad COFF version '%s'"), arg);
	  }

	int version = (int) version_long;

	if (version != 0 && version != 1 && version != 2)
	  as_fatal (_("Bad COFF version '%s'"), arg);
	/* FIXME -- not yet implemented.  */
	break;
      }
    case OPTION_CPU_VERSION:
      {
	cpu = lookup_version (arg);
	cpu_needs_set = 1;
	if (cpu == VNONE)
	  as_fatal (_("Bad CPU version '%s'"), arg);
	break;
      }
    case OPTION_ADDRESS_MODE:
      amode = far_mode;
      address_mode_needs_set = 1;
      break;
    case OPTION_STDERR_TO_FILE:
      {
	const char *filename = arg;
	if (freopen (filename, "w+", stderr) == NULL)
	  {
	    as_fatal (_("Can't redirect stderr to the file '%s'"), filename);
	  }
	break;
      }
    }

  return 1;
}

/* Create a "local" substitution string hash table for a new macro level
   Some docs imply that macros have to use .newblock in order to be able
   to re-use a local label.  We effectively do an automatic .newblock by
   deleting the local label hash between macro invocations.  */

void
tic54x_macro_start (void)
{
  macro_level++;

  if (macro_level >= MAX_SUBSYM_HASH)
    {
      macro_level--;
      as_fatal (_("Macro nesting is too deep"));
      return;
    }

  subsym_hash[macro_level] = subsym_htab_create ();
  local_label_hash[macro_level] = local_label_htab_create ();
}

#include <string.h>

void
tic54x_macro_info (const macro_entry *macro)
{
  const formal_entry *entry;

  for (entry = macro->formals; entry; entry = entry->next)
    {
      char *name = xstrndup (entry->name.ptr, entry->name.len);
      subsym_ent_t *ent = xmalloc (sizeof (*ent));

      memset(ent, 0, sizeof(*ent));

      ent->u.s = xstrndup (entry->actual.ptr, entry->actual.len);
      ent->freekey = 1;
      ent->freeval = 1;

      str_hash_insert (subsym_hash[macro_level], name, ent, 0);
    }
}

/* Get rid of this macro's .var's, arguments, and local labels.  */

void
tic54x_macro_end (void)
{
  /*
   * Guard against underflow of macro_level.
   * If macro_level is 0 or less, it indicates an attempt to end
   * a macro level that does not exist or is already below the base.
   * This prevents array out-of-bounds access (e.g., hash[-1]) and
   * ensures macro_level remains a valid index or state.
   * If this state is reached, it typically indicates a logic error
   * in how macro levels are managed, and further operations would lead to Undefined Behavior.
   * Returning early maintains reliability and security without altering
   * the intended behavior for valid macro levels.
   */
  if (macro_level <= 0)
  {
    return;
  }

  /*
   * At this point, macro_level is guaranteed to be a valid positive index
   * (e.g., 1 or greater), preventing array out-of-bounds access.
   */
  htab_delete (subsym_hash[macro_level]);
  subsym_hash[macro_level] = NULL;

  htab_delete (local_label_hash[macro_level]);
  local_label_hash[macro_level] = NULL;

  /*
   * Decrement macro_level. Since we've already ensured macro_level > 0,
   * it will safely become 0 or a positive value, avoiding negative indices
   * for subsequent operations.
   */
  --macro_level;
}

static int
subsym_symlen (const char *a, const char *ignore ATTRIBUTE_UNUSED)
{
  if (a == NULL)
    {
      return -1;
    }
  return (int) strlen (a);
}

/* Compare symbol A to string B.  */

static int
subsym_symcmp (char *a, char *b)
{
  if (a == NULL && b == NULL)
    {
      return 0;
    }
  if (a == NULL)
    {
      return -1;
    }
  if (b == NULL)
    {
      return 1;
    }
  return strcmp (a, b);
}

/* Return the index of the first occurrence of B in A, or zero if none
   assumes b is an integer char value as a string.  Index is one-based.  */

#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <limits.h>

static int
subsym_firstch (char *a, char *b)
{
  if (a == NULL || b == NULL) {
    return 0;
  }

  long lval;
  char *endptr;
  int val_to_search;

  errno = 0;

  lval = strtol(b, &endptr, 10);

  if (endptr == b) {
    val_to_search = 0;
  } else if (errno == ERANGE || lval < INT_MIN || lval > INT_MAX) {
    val_to_search = 0;
  } else {
    val_to_search = (int)lval;
  }

  char *tmp = strchr(a, val_to_search);

  return tmp ? (int)(tmp - a + 1) : 0;
}

/* Similar to firstch, but returns index of last occurrence of B in A.  */

static int
subsym_lastch (char *a, char *b)
{
  char *endptr;
  long val_long = strtol(b, &endptr, 10);

  // Mimic atoi's behavior for invalid or empty input strings:
  // if 'b' does not contain a valid number or is an empty string,
  // atoi returns 0. We preserve this behavior.
  if (endptr == b || *endptr != '\0') {
    val_long = 0;
  }

  // The 'int' argument to strrchr is converted to an 'unsigned char' internally
  // before comparison. This ensures that values outside the 0-255 range
  // (like -1 or values > 255) wrap around according to unsigned char arithmetic,
  // matching the original behavior when passing the result of atoi to strrchr.
  int search_char_val = (int)val_long;

  char *tmp = strrchr(a, search_char_val);

  return tmp ? (int)(tmp - a + 1) : 0;
}

/* Returns 1 if string A is defined in the symbol table (NOT the substitution
   symbol table).  */

static int
subsym_isdefed (char *a, char *ignore ATTRIBUTE_UNUSED)
{
  symbolS *symbolP = symbol_find (a);

  return symbolP != NULL;
}

/* Assign first member of comma-separated list B (e.g. "1,2,3") to the symbol
   A, or zero if B is a null string.  Both arguments *must* be substitution
   symbols, unsubstituted.  */

static int
subsym_ismember (char *sym, char *list)
{
  subsym_ent_t *listv;
  char *copied_value = NULL;
  char *separator_pos = NULL;
  char *elem_str = NULL;
  char *remainder_str = NULL;
  int return_value = 0;

  if (!list)
    {
      return 0;
    }

  listv = subsym_lookup (list, macro_level);
  if (!listv || listv->isproc)
    {
      as_bad (_("Undefined substitution symbol '%s'"), list);
      ignore_rest_of_line ();
      return 0;
    }

  copied_value = notes_strdup (listv->u.s);
  if (!copied_value)
    {
      as_bad (_("Memory allocation failed for substitution symbol '%s' value processing."), list);
      ignore_rest_of_line ();
      return 0;
    }

  elem_str = copied_value;
  separator_pos = strchr (copied_value, ',');

  if (separator_pos != NULL)
    {
      *separator_pos = '\0';
      remainder_str = separator_pos + 1;
    }
  else
    {
      remainder_str = "";
    }

  subsym_create_or_replace (sym, elem_str);
  subsym_create_or_replace (list, remainder_str);

  return_value = (*list != 0);

  free (copied_value);

  return return_value;
}

/* Return zero if not a constant; otherwise:
   1 if binary
   2 if octal
   3 if hexadecimal
   4 if character
   5 if decimal.  */

#include <string.h>
#include <ctype.h>

static int
subsym_iscons (const char *a, char *ignore ATTRIBUTE_UNUSED)
{
  expressionS expn;

  if (a == NULL)
    {
      return 0;
    }

  parse_expression (a, &expn);

  if (expn.X_op == O_constant)
    {
      size_t len = strlen (a);

      if (len == 0)
        {
          return 0;
        }

      switch (TOUPPER ((unsigned char)a[len - 1]))
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
	  break;
	}

      if (a[0] == '0' && len > 1)
	{
	  if (TOUPPER ((unsigned char)a[1]) == 'X')
	    return 3;
	  return 2;
	}
      return 5;
    }

  return 0;
}

/* Return 1 if A is a valid symbol name.  Expects string input.   */

static int
subsym_isname (char *a, char *ignore ATTRIBUTE_UNUSED)
{
  if (a == NULL)
    {
      return 0;
    }

  if (!is_name_beginner (*a))
    {
      return 0;
    }

  a++; // Move past the first character, which has already been validated as a 'beginner'

  while (*a)
    {
      if (!is_part_of_name (*a))
	{
	  return 0;
	}
      ++a;
    }

  return 1;
}

/* Return whether the string is a register; accepts ar0-7, unless .mmregs has
   been seen; if so, recognize any memory-mapped register.
   Note this does not recognize "A" or "B" accumulators.  */

static int
subsym_isreg (char *a)
{
  if (a == NULL)
    {
      return 0; /* A NULL string cannot be a registered symbol */
    }

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

static int
subsym_structacc (char *stag_name, char *ignore)
{
  (void)stag_name;
  (void)ignore;
  return 0;
}

#include <math.h> // Required for ceilf

static float
math_ceil (float arg1)
{
  return ceilf(arg1);
}

#include <math.h>
#include <limits.h>

static int
math_cvi (float arg1, float ignore ATTRIBUTE_UNUSED)
{
  if (isnan(arg1)) {
    // Return a well-defined integer for NaN. 0 is a common choice for undefined numeric results.
    return 0;
  }

  if (isinf(arg1)) {
    if (arg1 > 0) {
      // Positive infinity maps to the maximum representable integer value.
      return INT_MAX;
    } else {
      // Negative infinity maps to the minimum representable integer value.
      return INT_MIN;
    }
  }

  // Handle finite values that are outside the representable range of 'int'.
  // Compare the float value against the float representation of INT_MAX and INT_MIN
  // to ensure clamping for values that would cause undefined behavior upon conversion.
  if (arg1 >= (float)INT_MAX) {
    return INT_MAX;
  }
  if (arg1 <= (float)INT_MIN) {
    return INT_MIN;
  }

  // At this point, arg1 is finite and within the range where its integer
  // truncation is guaranteed to fit within an 'int' without undefined behavior.
  return (int)arg1;
}

#include <math.h>

static float
math_floor (float arg1)
{
  return floorf(arg1);
}

#include <math.h>

static float
math_fmod (float arg1, float arg2)
{
  return fmodf(arg1, arg2);
}

#include <math.h>

static int
math_int (float arg1, float ignore ATTRIBUTE_UNUSED)
{
  if (!isfinite(arg1)) {
    return 0;
  }
  return arg1 == truncf(arg1);
}

#include <math.h>

static float
math_round (float arg1)
{
  return roundf(arg1);
}

#include <math.h> // Required for isnanf

static int
math_sgn (float arg1, float ignore ATTRIBUTE_UNUSED)
{
  if (isnanf(arg1))
    {
      // Preserve original behavior for NaN: return 1
      return 1;
    }
  else if (arg1 < 0.0f)
    {
      return -1;
    }
  else if (arg1 > 0.0f)
    {
      return 1;
    }
  else /* arg1 is 0.0f (or -0.0f) */
    {
      return 0;
    }
}

#include <math.h>

static float
math_trunc (float arg1, float ignore ATTRIBUTE_UNUSED)
{
  return truncf(arg1);
}

#include <math.h>
#include <errno.h>

static float
math_acos (float arg1)
{
  if (arg1 < -1.0f || arg1 > 1.0f) {
    errno = EDOM;
    return nanf("");
  }

  return (float) acos (arg1);
}

#include <math.h>

static float
math_asin (float arg1)
{
  return asinf (arg1);
}

#include <math.h>

static float
math_atan (float arg1)
{
  return atanf (arg1);
}

#include <math.h>

static float
math_atan2 (float arg1, float arg2)
{
  return atan2f (arg1, arg2);
}

#include <math.h>

static float
math_cosh (float arg1)
{
  return (float) cosh (arg1);
}

#include <math.h> // Required for cosf

static float
math_cos (float arg1)
{
  return cosf(arg1);
}

static float
math_cvf (float arg1, float ignore ATTRIBUTE_UNUSED)
{
  return arg1;
}

#include <math.h>

static float
math_exp (float arg1)
{
  return expf(arg1);
}

static float
math_fabs (float value)
{
  return fabsf (value);
}

/* expr1 * 2^expr2.  */

#include <math.h>

static float
math_ldexp (float arg1, float arg2)
{
  return arg1 * powf(2.0f, arg2);
}

#include <math.h>
#include <errno.h>

static float
math_log10 (float arg1, float ignore ATTRIBUTE_UNUSED)
{
  (void)ignore;

  if (arg1 <= 0.0F) {
    if (arg1 == 0.0F) {
      errno = ERANGE;
      return -HUGE_VALF;
    } else {
      errno = EDOM;
      return NAN;
    }
  }

  return log10f(arg1);
}

#include <math.h>

static float
math_log (float arg1)
{
  return logf (arg1);
}

#include <math.h>

static float
math_max (float arg1, float arg2)
{
  return fmaxf(arg1, arg2);
}

static float
math_min (float arg1, float arg2)
{
  if (arg1 < arg2)
  {
    return arg1;
  }
  else
  {
    return arg2;
  }
}

#include <math.h>

static float
math_pow (float arg1, float arg2)
{
  return powf (arg1, arg2);
}

#include <math.h>

static float
math_sin (float arg1)
{
  return sinf (arg1);
}

#include <math.h>
#include <errno.h>

static float
math_sinh (float arg1, float ignore ATTRIBUTE_UNUSED)
{
  float result;

  errno = 0; 

  result = sinhf(arg1);

  if (errno == ERANGE) {
  }

  return result;
}

#include <math.h>

static float
math_sqrt (float value)
{
  return sqrtf(value);
}

#include <math.h>

static float
math_tan (float arg1, float ignore ATTRIBUTE_UNUSED)
{
  return tanf (arg1);
}

#include <math.h>

static float
math_tanh (float arg1)
{
  return tanhf(arg1);
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

static void
_md_populate_insn_template_hash(htab_t *hash_ptr, const insn_template *templates)
{
  *hash_ptr = str_htab_create();
  for (const insn_template *tm = templates; tm->name; tm++)
    {
      str_hash_insert(*hash_ptr, tm->name, (void *)tm, 0);
    }
}

static void
_md_populate_tic54x_symbol_hash(htab_t *hash_ptr, const tic54x_symbol *symbols)
{
  *hash_ptr = str_htab_create();
  for (const tic54x_symbol *sym = symbols; sym->name; sym++)
    {
      str_hash_insert(*hash_ptr, sym->name, (void *)sym, 0);
    }
}

static void
_md_populate_misc_symbol_hash(htab_t *hash_ptr, const char *const *symbols)
{
  *hash_ptr = str_htab_create();
  for (const char *const *symname = symbols; *symname; symname++)
    {
      str_hash_insert(*hash_ptr, *symname, (void *)*symname, 0);
    }
}

static void
_md_populate_regs_with_symbols(htab_t *hash_ptr, const tic54x_symbol *regs)
{
  *hash_ptr = str_htab_create();
  for (const tic54x_symbol *sym = regs; sym->name; sym++)
    {
      symbolS *symbolP = symbol_new(sym->name, absolute_section,
                                     &zero_address_frag, sym->value);
      SF_SET_LOCAL(symbolP);
      symbol_table_insert(symbolP);
      str_hash_insert(*hash_ptr, sym->name, (void *)sym, 0);
    }
}

static void
_md_populate_subsym_procs_hash(htab_t *hash_ptr, const subsym_proc_entry *procs)
{
  *hash_ptr = subsym_htab_create();
  for (const subsym_proc_entry *subsym_proc = procs; subsym_proc->name; subsym_proc++)
    {
      subsym_ent_t *ent = xmalloc(sizeof(*ent));
      ent->u.p = subsym_proc;
      ent->freekey = 0;
      ent->freeval = 0;
      ent->isproc = 1;
      ent->ismath = subsym_proc->type != 0;
      str_hash_insert(*hash_ptr, subsym_proc->name, (void *)ent, 0);
    }
}

void
md_begin (void)
{
  local_label_id = 0;

  char *env_path_value = getenv("TIC54X_DIR");
  if (env_path_value == NULL)
    {
      env_path_value = getenv("A_DIR");
    }

  if (env_path_value != NULL)
    {
      char *dir_list_copy = notes_strdup(env_path_value);
      if (dir_list_copy == NULL)
        {
          return;
        }

      char *current_path = dir_list_copy;
      char *next_separator;

      do
        {
          next_separator = strchr(current_path, ';');
          if (next_separator != NULL)
            {
              *next_separator = '\0';
            }

          if (*current_path != '\0')
            {
              add_include_dir(current_path);
            }

          if (next_separator != NULL)
            {
              current_path = next_separator + 1;
            }
        }
      while (next_separator != NULL);

      free(dir_list_copy);
    }

  _md_populate_insn_template_hash(&op_hash, tic54x_optab);
  _md_populate_insn_template_hash(&parop_hash, tic54x_paroptab);

  _md_populate_regs_with_symbols(&reg_hash, tic54x_regs);
  for (const tic54x_symbol *sym = tic54x_mmregs; sym->name; sym++)
    {
      str_hash_insert(reg_hash, sym->name, (void *)sym, 0);
    }
  _md_populate_tic54x_symbol_hash(&mmreg_hash, tic54x_mmregs);

  _md_populate_tic54x_symbol_hash(&cc_hash, tic54x_condition_codes);
  _md_populate_tic54x_symbol_hash(&cc2_hash, tic54x_cc2_codes);
  _md_populate_tic54x_symbol_hash(&cc3_hash, tic54x_cc3_codes);

  _md_populate_tic54x_symbol_hash(&sbit_hash, tic54x_status_bits);

  _md_populate_misc_symbol_hash(&misc_symbol_hash, tic54x_misc_symbols);

  local_label_hash[0] = local_label_htab_create();
  _md_populate_subsym_procs_hash(&subsym_hash[0], subsym_procs);
  subsym_recurse_hash = str_htab_create();
  stag_hash = str_htab_create();
}

void
tic54x_md_end (void)
{
  htab_t *hash_tables[] = {
    &stag_hash,
    &subsym_recurse_hash,
    &misc_symbol_hash,
    &sbit_hash,
    &cc3_hash,
    &cc2_hash,
    &cc_hash,
    &mmreg_hash,
    &reg_hash,
    &parop_hash,
    &op_hash,
    NULL
  };

  for (size_t i = 0; hash_tables[i] != NULL; ++i)
    {
      if (*hash_tables[i] != NULL)
        {
          htab_delete (*hash_tables[i]);
          *hash_tables[i] = NULL;
        }
    }

  while (macro_level != -1)
    {
      tic54x_macro_end ();
    }
  macro_level = 0;
}

#include <string.h>

static int
is_accumulator (struct opstruct *operand)
{
  if (operand == NULL || operand->buf == NULL)
    {
      return 0;
    }

  return strcasecmp (operand->buf, "a") == 0
    || strcasecmp (operand->buf, "b") == 0;
}

/* Return the number of operands found, or -1 on error, copying the
   operands into the given array and the accompanying expressions into
   the next array.  */

static char *
find_matching_paren (char *open_paren)
{
  if (!open_paren || *open_paren != '(')
    return NULL;

  int balance = 1;
  char *ptr = open_paren + 1;

  while (*ptr != '\0')
    {
      if (*ptr == '(')
	    ++balance;
      else if (*ptr == ')')
	    --balance;

      if (balance == 0)
	    return ptr;
      ++ptr;
    }
  return NULL; // Unbalanced parentheses or missing closing parenthesis
}

static int
extract_single_operand (char **line_ptr, char *operand_str, size_t buf_size)
{
  char *lptr = *line_ptr;
  char *op_start, *op_end;
  int paren_balance = 0;

  while (is_whitespace (*lptr))
    ++lptr;

  op_start = lptr;

  while (1)
    {
      if (*lptr == '\0')
	{
	  if (paren_balance != 0)
	    {
	      as_bad (_("Unbalanced parenthesis in operand"));
	      return -1;
	    }
	  op_end = lptr;
	  break;
	}
      if (*lptr == '(')
	{
	  ++paren_balance;
	}
      else if (*lptr == ')')
	{
	  --paren_balance;
	  if (paren_balance < 0)
	    {
	      as_bad (_("Mismatched closing parenthesis in operand"));
	      return -1;
	    }
	}
      else if (!paren_balance && *lptr == ',')
	{
	  op_end = lptr;
	  break;
	}
      ++lptr;
    }

  if (op_end == op_start)
    {
      operand_str[0] = '\0';
    }
  else
    {
      size_t len = op_end - op_start;
      if (len >= buf_size)
	{
	  as_bad (_("Operand too long"));
	  return -1;
	}
      strncpy (operand_str, op_start, len);
      operand_str[len] = '\0';

      while (len > 0 && is_whitespace (operand_str[len - 1]))
	operand_str[--len] = '\0';
    }

  *line_ptr = lptr;
  return 0;
}

static int
get_operands (struct opstruct operands[], char *line)
{
  char *lptr = line;
  int numexp = 0;
  int expecting_operand = 0;
  int i;

  while (numexp < MAX_OPERANDS)
    {
      char operand_buf[MAX_OPERAND_BUF_SIZE];

      if (extract_single_operand (&lptr, operand_buf, sizeof(operand_buf)) == -1)
	{
	  return -1;
	}

      if (operand_buf[0] == '\0')
	{
	  if (expecting_operand || *lptr == ',')
	    {
	      as_bad (_("Expecting operand after ','"));
	      return -1;
	    }
	  if (is_end_of_stmt(*lptr))
	    break;
	  // If empty operand found, not expecting one, and not end of statement,
	  // and not a comma, it implies unexpected characters. Break to handle as junk.
	  break;
	}
      else
	{
	  strcpy (operands[numexp].buf, operand_buf);
	  ++numexp;
	  expecting_operand = 0;
	}

      if (*lptr == ',')
	{
	  ++lptr;
	  if (*lptr == '\0')
	    {
	      as_bad (_("Expecting operand after ','"));
	      return -1;
	    }
	  expecting_operand = 1;
	}
      else if (is_end_of_stmt (*lptr))
	{
	  break;
	}
      else // Non-empty operand, but no comma or end of statement means unparsed junk
      {
          break;
      }
    }

  if (numexp == MAX_OPERANDS)
    {
      char *temp_lptr = lptr;
      while (is_whitespace(*temp_lptr)) ++temp_lptr;
      if (!is_end_of_stmt(*temp_lptr)) {
          as_bad(_("Too many operands"));
          return -1;
      }
    }

  while (is_whitespace (*lptr))
    ++lptr;
  if (!is_end_of_stmt (*lptr))
    {
      as_bad (_("Extra junk on line"));
      return -1;
    }

  for (i = 0; i < numexp; i++)
    {
      memset (&operands[i].exp, 0, sizeof (operands[i].exp));
      if (operands[i].buf[0] == '#')
	{
	  parse_expression (operands[i].buf + 1, &operands[i].exp);
	}
      else if (operands[i].buf[0] == '@')
	{
	  parse_expression (operands[i].buf + 1, &operands[i].exp);
	}
      else if (operands[i].buf[0] == '*')
	{
	  char *indirect_str = operands[i].buf;
	  char *paren = strchr (indirect_str + 1, '(');

	  if (paren && (paren + 1 < indirect_str + MAX_OPERAND_BUF_SIZE) && paren[1] == '#')
	    {
	      *++paren = '(';
	    }

	  if (paren != NULL)
	    {
	      char *expr_start = paren;
	      char *matching_paren_ptr = find_matching_paren (expr_start);

	      if (matching_paren_ptr == NULL)
		{
		  as_bad (_("Badly formed address expression: unbalanced or missing parentheses"));
		  return -1;
		}

	      char original_char_at_end = *matching_paren_ptr;
	      *matching_paren_ptr = '\0';
	      parse_expression (expr_start, &operands[i].exp);
	      *matching_paren_ptr = original_char_at_end;
	    }
	  else
	    {
	      parse_expression (indirect_str + 1, &operands[i].exp);
	    }
	}
      else
	parse_expression (operands[i].buf, &operands[i].exp);
    }

  return numexp;
}

/* Predicates for different operand types.  */

static int
is_immediate (struct opstruct *operand)
{
  if (operand == NULL || operand->buf == NULL)
    {
      /*
       * An operand cannot be considered "immediate" if the operand structure
       * itself is null or if its buffer pointer is null.
       * Returning 0 (false) in these cases prevents null pointer dereferences,
       * improving reliability and security, and aligns with the semantic
       * expectation that an invalid input is not an immediate value.
       */
      return 0;
    }

  return *operand->buf == '#';
}

/* This is distinguished from immediate because some numbers must be constants
   and must *not* have the '#' prefix.  */

static int
is_absolute (struct opstruct *operand)
{
  if (operand == NULL)
    {
      return 0;
    }
  return operand->exp.X_op == O_constant && !is_immediate (operand);
}

/* Is this an indirect operand?  */

static int
is_indirect (struct opstruct *operand)
{
  if (operand == NULL)
    {
      return 0;
    }

  if (operand->buf == NULL)
    {
      return 0;
    }

  return operand->buf[0] == '*';
}

/* Is this a valid dual-memory operand?  */

static int
is_dual (struct opstruct *operand)
{
  if (operand == NULL || operand->buf == NULL)
    {
      return 0;
    }

  if (!is_indirect (operand))
    {
      return 0;
    }

  if (strlen(operand->buf) < 4 || strncasecmp (operand->buf, "*ar", 3) != 0)
    {
      return 0;
    }

  char arf_char = operand->buf[3];
  if (!isdigit(arf_char))
    {
      return 0;
    }
  int arf = arf_char - '0';

  if (arf < 2 || arf > 5)
    {
      return 0;
    }

  const char *suffix = operand->buf + 4;
  if (*suffix == '\0' ||
      strcasecmp (suffix, "-") == 0 ||
      strcasecmp (suffix, "+") == 0 ||
      strcasecmp (suffix, "+0%") == 0)
    {
      return 1;
    }

  return 0;
}

static bool
is_mmreg (struct opstruct *operand)
{
  if (operand == NULL)
    {
      return false;
    }

  if (is_absolute (operand) || is_immediate (operand))
    {
      return true;
    }

  if (operand->buf == NULL)
    {
      return false;
    }

  return str_hash_find (mmreg_hash, operand->buf) != 0;
}

static int
is_type (struct opstruct *operand, enum optype type)
{
  if (operand == NULL)
    {
      return 0;
    }

  switch (type)
    {
    case OP_None:
      if (operand->buf == NULL)
        {
          return 0;
        }
      return operand->buf[0] == 0;

    case OP_Xmem:
    case OP_Ymem:
      return is_dual (operand);

    case OP_Sind:
      return is_indirect (operand);

    case OP_xpmad_ms7:
      return is_immediate (operand);

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
      return !is_immediate (operand);

    case OP_MMRY:
    case OP_MMRX:
      return is_mmreg (operand);

    case OP_SRC:
    case OP_SRC1:
    case OP_RND:
    case OP_DST:
      return is_accumulator (operand);

    case OP_B:
      if (operand->buf == NULL)
        {
          return 0;
        }
      return is_accumulator (operand) && TOUPPER (operand->buf[0]) == 'B';

    case OP_A:
      if (operand->buf == NULL)
        {
          return 0;
        }
      return is_accumulator (operand) && TOUPPER (operand->buf[0]) == 'A';

    case OP_ARX:
      if (operand->buf == NULL || strlen(operand->buf) < 3)
        {
          return 0;
        }
      return strncasecmp ("ar", operand->buf, 2) == 0 && ISDIGIT (operand->buf[2]);

    case OP_SBIT:
      if (operand->buf == NULL)
        {
          return is_absolute (operand);
        }
      return str_hash_find (sbit_hash, operand->buf) != 0 || is_absolute (operand);

    case OP_CC:
      if (operand->buf == NULL)
        {
          return 0;
        }
      return str_hash_find (cc_hash, operand->buf) != 0;

    case OP_CC2:
      if (operand->buf == NULL)
        {
          return 0;
        }
      return str_hash_find (cc2_hash, operand->buf) != 0;

    case OP_CC3:
      if (operand->buf == NULL)
        {
          return is_immediate (operand) || is_absolute (operand);
        }
      return str_hash_find (cc3_hash, operand->buf) != 0
             || is_immediate (operand) || is_absolute (operand);

    case OP_16:
      return (is_immediate (operand) || is_absolute (operand))
             && operand->exp.X_add_number == 16;

    case OP_N:
      return (is_absolute (operand) || is_immediate (operand)) ||
             (operand->buf != NULL && (strcasecmp ("st0", operand->buf) == 0 ||
                                       strcasecmp ("st1", operand->buf) == 0));

    case OP_12:
    case OP_123:
    case OP_BITC:
    case OP_031:
    case OP_k8:
      return is_absolute (operand) || is_immediate (operand);

    case OP_SHFT:
      return (is_immediate (operand) || is_absolute (operand))
             && operand->exp.X_add_number >= 0 && operand->exp.X_add_number < 16;

    case OP_SHIFT:
      return (is_immediate (operand) || is_absolute (operand))
             && operand->exp.X_add_number != 16;

    case OP_k8u:
      return is_immediate (operand)
             && operand->exp.X_op == O_constant
             && operand->exp.X_add_number >= 0
             && operand->exp.X_add_number < 256;

    case OP_k5:
    case OP_k3:
    case OP_k9:
      return is_immediate (operand);

    case OP_T:
      return operand->buf != NULL && (strcasecmp ("t", operand->buf) == 0 ||
                                      strcasecmp ("treg", operand->buf) == 0);

    case OP_TS:
      return operand->buf != NULL && strcasecmp ("ts", operand->buf) == 0;

    case OP_ASM:
      return operand->buf != NULL && strcasecmp ("asm", operand->buf) == 0;

    case OP_TRN:
      return operand->buf != NULL && strcasecmp ("trn", operand->buf) == 0;

    case OP_DP:
      return operand->buf != NULL && strcasecmp ("dp", operand->buf) == 0;

    case OP_ARP:
      return operand->buf != NULL && strcasecmp ("arp", operand->buf) == 0;

    default:
      return 0;
    }
}

static int
operands_match (tic54x_insn *insn,
		struct opstruct *actual_operands,
		int actual_operand_count,
		const enum optype *ref_template_types,
		int min_template_operands,
		int ref_template_total_count)
{
  int actual_op_idx = 0;
  int template_op_idx = 0;

  if (actual_operand_count == 0 && min_template_operands == 0)
    return 1;

  while (actual_op_idx < actual_operand_count && template_op_idx < ref_template_total_count)
    {
      while (!is_type (&actual_operands[actual_op_idx], OPTYPE (ref_template_types[template_op_idx])))
	{
	  if (ref_template_types[template_op_idx] & OPT)
	    {
	      ++template_op_idx;
	      if (template_op_idx >= ref_template_total_count)
		return 0;
	    }
	  else
	    {
	      return 0;
	    }
	}

      actual_operands[actual_op_idx].type = OPTYPE (ref_template_types[template_op_idx]);
      ++template_op_idx;
      ++actual_op_idx;
    }

  if (actual_op_idx == actual_operand_count)
    {
      while (template_op_idx < ref_template_total_count)
	{
	  if (!(ref_template_types[template_op_idx] & OPT))
		return 0;

	  if (OPTYPE (ref_template_types[template_op_idx]) == OP_DST)
		insn->using_default_dst = 1;

	  ++template_op_idx;
	}
      return actual_operand_count >= min_template_operands;
    }
  else
    {
      return 0;
    }
}

/* 16-bit direct memory address
   Explicit dmad operands are always in last word of insn (usually second
   word, but bumped to third if lk addressing is used)

   We allow *(dmad) notation because the TI assembler allows it.

   XPC_CODE:
   0 for 16-bit addresses
   1 for full 23-bit addresses
   2 for the upper 7 bits of a 23-bit address (LDX).  */

#include <string.h>

#define DMAD_OP_OFFSET_BASE 1
#define DMAD_RELOC_NCHARS_DEFAULT 2
#define DMAD_RELOC_XPC1_NCHARS 4
#define DMAD_WORDS_XPC1_SPECIAL 1

#define DMAD_XPC1_WORD0_PRESERVE_MASK 0xFF80
#define DMAD_XPC1_HIGH_VALUE_MASK 0x7F
#define DMAD_XPC1_HIGH_VALUE_SHIFT 16
#define DMAD_WORD_LOW_MASK 0xFFFF

static int
encode_dmad (tic54x_insn *insn, struct opstruct *operand, int xpc_code)
{
  int op = DMAD_OP_OFFSET_BASE + insn->is_lkaddr;

  if (is_indirect (operand) && operand->buf[strlen (operand->buf) - 1] != ')')
    {
      as_bad (_("Invalid dmad syntax '%s'"), operand->buf);
      return 0;
    }

  insn->opcode[op].addr_expr = operand->exp;

  if (insn->opcode[op].addr_expr.X_op == O_constant)
    {
      valueT value = insn->opcode[op].addr_expr.X_add_number;

      switch (xpc_code)
        {
          case 1:
            insn->opcode[0].word = (insn->opcode[0].word & DMAD_XPC1_WORD0_PRESERVE_MASK)
                                   | ((value >> DMAD_XPC1_HIGH_VALUE_SHIFT) & DMAD_XPC1_HIGH_VALUE_MASK);
            insn->opcode[1].word = value & DMAD_WORD_LOW_MASK;
            break;
          case 2:
            insn->opcode[op].word = (value >> DMAD_XPC1_HIGH_VALUE_SHIFT) & DMAD_WORD_LOW_MASK;
            break;
          default:
            insn->opcode[op].word = value;
            break;
        }
    }
  else
    {
      insn->opcode[op].word = 0;
      insn->opcode[op].r_nchars = DMAD_RELOC_NCHARS_DEFAULT;
      insn->opcode[op].unresolved = 1;

      if (amode == c_mode)
        {
          insn->opcode[op].r_type = BFD_RELOC_TIC54X_16_OF_23;
        }
      else
        {
          switch (xpc_code)
            {
              case 1:
                insn->opcode[0].addr_expr = operand->exp;
                insn->opcode[0].r_type = BFD_RELOC_TIC54X_23;
                insn->opcode[0].r_nchars = DMAD_RELOC_XPC1_NCHARS;
                insn->opcode[0].unresolved = 1;
                insn->words = DMAD_WORDS_XPC1_SPECIAL;
                break;
              case 2:
                insn->opcode[op].r_type = BFD_RELOC_TIC54X_MS7_OF_23;
                break;
              default:
                insn->opcode[op].r_type = BFD_RELOC_TIC54X_16_OF_23;
                break;
            }
        }
    }

  return 1;
}

/* 7-bit direct address encoding.  */

static int
encode_address (tic54x_insn *insn, struct opstruct *operand)
{
  insn->opcode[0].addr_expr = operand->exp;

  switch (operand->exp.X_op)
    {
    case O_constant:
      insn->opcode[0].word |= (operand->exp.X_add_number & 0x7F);
      break;

    case O_register:
      as_bad (_("Use the .mmregs directive to use memory-mapped register names such as '%s'"), operand->buf);
      return 0;

    default:
      insn->opcode[0].r_nchars = 1;
      insn->opcode[0].r_type = BFD_RELOC_TIC54X_PARTLS7;
      insn->opcode[0].unresolved = 1;
      break;
    }

  return 1;
}

static int
encode_indirect(tic54x_insn *insn, struct opstruct *operand)
{
  int arf;
  int mod = -1; /* Initialize to an invalid value */
  int result = 1;

  if (insn->is_lkaddr)
    {
      /* lk addresses always go in the second insn word.  */
      const char second_char = TOUPPER(operand->buf[1]);
      const char *percent_char = strchr(operand->buf, '%');

      if (second_char == 'A')
        {
          mod = 12;
          arf = operand->buf[3] - '0';
        }
      else if (operand->buf[1] == '(')
        {
          mod = 15;
          arf = 0;
        }
      else if (percent_char != NULL)
        {
          mod = 14;
          arf = operand->buf[4] - '0';
        }
      else
        {
          mod = 13;
          arf = operand->buf[4] - '0';
        }

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
  else if (strncasecmp(operand->buf, "*sp (", 5) == 0) /* Corrected length to 5 to include space */
    {
      /* Stack offsets look the same as 7-bit direct addressing.  */
      return encode_address(insn, operand);
    }
  else
    {
      arf = (TOUPPER(operand->buf[1]) == 'A' ? operand->buf[3] : operand->buf[4]) - '0';

      /* Determine `mod` based on the operand buffer content */
      const char *buf_ptr = operand->buf;
      size_t buf_len = strlen(buf_ptr);

      if (buf_ptr[1] == '+')
        {
          mod = 3; /* *+ARx */
          if (insn->tm->flags & FL_SMR)
            {
              as_warn(_("Address mode *+ARx is write-only. Results of reading are undefined."));
            }
        }
      else if (buf_len == 4 && buf_ptr[0] == '*' && TOUPPER(buf_ptr[1]) == 'A' && isdigit(buf_ptr[3]))
        {
          mod = 0; /* *ARx */
        }
      else if (buf_len == 5)
        {
          if (buf_ptr[4] == '-')
            mod = 1; /* *ARx- */
          else if (buf_ptr[4] == '+')
            mod = 2; /* *ARx+ */
        }
      else if (buf_len == 6)
        {
          if (buf_ptr[5] == '0')
            {
              if (buf_ptr[4] == '-')
                mod = 5; /* *ARx-0 */
              else if (buf_ptr[4] == '+')
                mod = 6; /* *ARx+0 */
            }
          else if (buf_ptr[5] == '%')
            {
              if (buf_ptr[4] == '-')
                mod = 8; /* *ARx-% */
              else if (buf_ptr[4] == '+')
                mod = 10; /* *ARx+% */
            }
        }
      else if (buf_len == 7)
        {
          if (TOUPPER(buf_ptr[6]) == 'B')
            {
              if (buf_ptr[4] == '-')
                mod = 4; /* *ARx-0B */
              else if (buf_ptr[4] == '+')
                mod = 7; /* *ARx+0B */
            }
          else if (TOUPPER(buf_ptr[6]) == '%')
            {
              if (buf_ptr[4] == '-')
                mod = 9; /* *ARx-0% */
              else if (buf_ptr[4] == '+')
                mod = 11; /* *ARx+0% */
            }
        }

      if (mod == -1)
        {
          as_bad(_("Unrecognized indirect address format \"%s\""), operand->buf);
          result = 0;
        }
    }

  if (result == 1)
    {
      insn->opcode[0].word |= 0x80 | (mod << 3) | arf;
    }

  return result;
}

static long
interpret_operand_value_tic54x(long raw_value, int min_range, int max_range)
{
  if ((raw_value & 0x8000) && min_range == -32768 && max_range == 32767)
    {
      return (long)((short)raw_value);
    }
  return raw_value;
}

static int
get_relocation_info_tic54x(unsigned short mask, bfd_reloc_code_real_type *rtype_out, int *size_out)
{
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
      return 0;
    }

  *rtype_out = rtype;
  *size_out = size;
  return 1;
}

static int
encode_integer (tic54x_insn *insn,
		struct opstruct *operand,
		int which,
		int min,
		int max,
		unsigned short mask)
{
  insn->opcode[which].addr_expr = operand->exp;

  if (operand->exp.X_op == O_constant)
    {
      long raw_parse_value = operand->exp.X_add_number;
      long integer_value = interpret_operand_value_tic54x(raw_parse_value, min, max);

      if (integer_value >= min && integer_value <= max)
        {
          insn->opcode[which].word |= (integer_value & mask);
          return 1;
        }
      else
        {
          as_bad (_("Operand '%s' out of range (%d <= x <= %d)"),
                  operand->buf, min, max);
          return 0;
        }
    }
  else
    {
      bfd_reloc_code_real_type rtype;
      int size;

      if (!get_relocation_info_tic54x(mask, &rtype, &size))
        {
          as_bad (_("Error: Unhandled mask for relocation type determination."));
          return 0;
        }

      insn->opcode[which].r_nchars = size;
      insn->opcode[which].r_type = rtype;
      insn->opcode[which].unresolved = 1;
      return 1;
    }
}

static int
encode_condition (tic54x_insn *insn, struct opstruct *operand)
{
#define CC_GROUP 0x40
#define CC_ACC   0x08
#define CATG_A1  0x07
#define CATG_B1  0x30
#define CATG_A2  0x30
#define CATG_B2  0x0C
#define CATG_C2  0x03

  tic54x_symbol *cc_symbol = str_hash_find (cc_hash, operand->buf);
  if (!cc_symbol)
    {
      as_bad (_("Unrecognized condition code \"%s\""), operand->buf);
      return 0;
    }

  unsigned int current_encoded_conditions = insn->opcode[0].word;
  unsigned int new_condition_flags = cc_symbol->value;

  if ((current_encoded_conditions & 0xFF) != 0)
    {
      if ((current_encoded_conditions & CC_GROUP) != (new_condition_flags & CC_GROUP))
        {
          as_bad (_("Condition \"%s\" does not match preceding group"),
                  operand->buf);
          return 0;
        }

      if (current_encoded_conditions & CC_GROUP)
        {
          if ((current_encoded_conditions & CC_ACC) != (new_condition_flags & CC_ACC))
            {
              as_bad (_("Condition \"%s\" uses a different accumulator from "
                        "a preceding condition"),
                      operand->buf);
              return 0;
            }
          if ((current_encoded_conditions & CATG_A1) && (new_condition_flags & CATG_A1))
            {
              as_bad (_("Only one comparison conditional allowed"));
              return 0;
            }
          if ((current_encoded_conditions & CATG_B1) && (new_condition_flags & CATG_B1))
            {
              as_bad (_("Only one overflow conditional allowed"));
              return 0;
            }
        }
      else
        {
          if (   ((current_encoded_conditions & CATG_A2) && (new_condition_flags & CATG_A2))
              || ((current_encoded_conditions & CATG_B2) && (new_condition_flags & CATG_B2))
              || ((current_encoded_conditions & CATG_C2) && (new_condition_flags & CATG_C2)))
            {
              as_bad (_("Duplicate %s conditional"), operand->buf);
              return 0;
            }
        }
    }

  insn->opcode[0].word |= new_condition_flags;
  return 1;
}

#define CC3_SHIFT_AMOUNT 8
#define CC3_VALID_BITS_MASK 0x0300

static int
encode_cc3 (tic54x_insn *insn, struct opstruct *operand)
{
  if (insn == NULL || operand == NULL)
    {
      return 0;
    }

  tic54x_symbol *cc3_symbol = str_hash_find (cc3_hash, operand->buf);
  int value = cc3_symbol ? cc3_symbol->value : operand->exp.X_add_number << CC3_SHIFT_AMOUNT;

  if ((value & CC3_VALID_BITS_MASK) != value)
    {
      as_bad (_("Unrecognized condition code \"%s\""), operand->buf);
      return 0;
    }

  insn->opcode[0].word |= value;
  return 1;
}

static int
encode_arx (tic54x_insn *insn, struct opstruct *operand)
{
  if (insn == NULL || operand == NULL || operand->buf == NULL)
    {
      as_bad (_("Internal error: Invalid input for auxiliary register encoding."));
      return 0;
    }

  const char *buf = operand->buf;
  int arf;
  size_t len = strlen(buf);

  if (len < 3)
    {
      as_bad (_("Invalid auxiliary register (use AR0-AR7)"));
      return 0;
    }

  if (strncasecmp (buf, "ar", 2) != 0)
    {
      as_bad (_("Invalid auxiliary register (use AR0-AR7)"));
      return 0;
    }

  char digit_char = buf[2];
  if (digit_char >= '0' && digit_char <= '7')
    {
      arf = digit_char - '0';
    }
  else
    {
      as_bad (_("Invalid auxiliary register (use AR0-AR7)"));
      return 0;
    }

  insn->opcode[0].word |= arf;
  return 1;
}

static int
encode_cc2 (tic54x_insn *insn, const struct opstruct *operand)
{
  if (insn == NULL)
    {
      as_bad (_("Internal error: Instruction object is NULL."));
      return 0;
    }

  if (operand == NULL)
    {
      as_bad (_("Internal error: Operand object is NULL."));
      return 0;
    }

  if (operand->buf == NULL)
    {
      as_bad (_("Internal error: Operand buffer is NULL."));
      return 0;
    }

  const tic54x_symbol *cc2 = str_hash_find (cc2_hash, operand->buf);

  if (cc2 == NULL)
    {
      as_bad (_("Unrecognized condition code \"%s\""), operand->buf);
      return 0;
    }

  insn->opcode[0].word |= cc2->value;
  return 1;
}

static int
encode_operand (tic54x_insn *insn, enum optype type, struct opstruct *operand)
{
  const int opcode_target_idx = ((insn->tm->flags & FL_EXT) != 0) ? (1 + insn->is_lkaddr) : 0;

  if (type == OP_MMR && operand->exp.X_op != O_constant)
    {
      if (insn->is_lkaddr)
	{
	  as_bad (_("lk addressing modes are invalid for memory-mapped "
		    "register addressing"));
	  return 0;
	}
      type = OP_Smem;
      if (strncasecmp (operand->buf, "*+ar", 4) == 0)
	{
	  as_warn (_("Address mode *+ARx is not allowed in memory-mapped "
		     "register addressing.  Resulting behavior is "
		     "undefined."));
	}
    }

  switch (type)
    {
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
      return encode_dmad (insn, operand, 0);

    case OP_SRC:
      if (TOUPPER (*operand->buf) == 'B')
	{
	  insn->opcode[opcode_target_idx].word |= (1 << 9);
	  if (insn->using_default_dst)
	    insn->opcode[opcode_target_idx].word |= (1 << 8);
	}
      return 1;

    case OP_RND:
      if (!((TOUPPER (operand->buf[0]) == 'B') ^
	    ((insn->opcode[0].word & (1 << 8)) != 0)))
	{
	  as_bad (_("Destination accumulator for each part of this parallel "
		    "instruction must be different"));
	  return 0;
	}
      return 1;

    case OP_SRC1:
    case OP_DST:
      if (TOUPPER (operand->buf[0]) == 'B')
	insn->opcode[opcode_target_idx].word |= (1 << 8);
      return 1;

    case OP_Xmem:
    case OP_Ymem:
      {
	const char *buf = operand->buf;
	size_t len = strlen(buf);

	if (len < 4 || strncmp(buf, "*ar", 3) != 0 || !isdigit(buf[3])) {
	    as_bad(_("Invalid indexed address operand format \"%s\""), buf);
	    return 0;
	}

	int mod_val;
	if (len == 4) {
	    mod_val = 0;
	} else if (len >= 5 && buf[4] == '-') {
	    mod_val = 1;
	} else if (len == 5 && buf[4] == '+') {
	    mod_val = 2;
	} else if (len >= 6 && buf[4] == '+') {
	    mod_val = 3;
	} else {
	    as_bad(_("Invalid indexed address operand modifier in \"%s\""), buf);
	    return 0;
	}

	int arf = (buf[3] - '0') - 2;
	int code = (mod_val << 2) | arf;
	insn->opcode[0].word |= (code << (type == OP_Xmem ? 4 : 0));
	return 1;
      }

    case OP_Lmem:
    case OP_Smem:
      if (!is_indirect (operand))
	return encode_address (insn, operand);
    case OP_Sind:
      return encode_indirect (insn, operand);

    case OP_xpmad_ms7:
      return encode_dmad (insn, operand, 2);
    case OP_xpmad:
      return encode_dmad (insn, operand, 1);
    case OP_PA:
    case OP_pmad:
      return encode_dmad (insn, operand, 0);

    case OP_ARX:
      return encode_arx (insn, operand);

    case OP_MMRX:
    case OP_MMRY:
    case OP_MMR:
      {
	int value = operand->exp.X_add_number;

	if (type == OP_MMR)
	  insn->opcode[0].word |= value;
	else
	  {
	    if (value < 16 || value > 24)
	      {
		as_bad (_("Memory mapped register \"%s\" out of range"),
			operand->buf);
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
      return encode_integer (insn, operand, opcode_target_idx, 0, 15, 0xF);
    case OP_SHIFT:
      return encode_integer (insn, operand, opcode_target_idx, -16, 15, 0x1F);
    case OP_lk:
      return encode_integer (insn, operand, 1 + insn->is_lkaddr, -32768, 32767, 0xFFFF);
    case OP_CC:
      return encode_condition (insn, operand);
    case OP_CC2:
      return encode_cc2 (insn, operand);
    case OP_CC3:
      return encode_cc3 (insn, operand);
    case OP_BITC:
      return encode_integer (insn, operand, 0, 0, 15, 0xF);
    case OP_k8:
      return encode_integer (insn, operand, 0, -128, 127, 0xFF);

    case OP_123:
      {
	int value = operand->exp.X_add_number;
	if (value < 1 || value > 3)
	  {
	    as_bad (_("Invalid operand (use 1, 2, or 3)"));
	    return 0;
	  }
	int code = (value == 1) ? 0 : ((value == 2) ? 0x2 : 0x1);
	insn->opcode[0].word |= (code << 8);
	return 1;
      }
    case OP_031:
      return encode_integer (insn, operand, 0, 0, 31, 0x1F);
    case OP_k8u:
      return encode_integer (insn, operand, 0, 0, 255, 0xFF);
    case OP_lku:
      return encode_integer (insn, operand, 1 + insn->is_lkaddr, 0, 65535, 0xFFFF);

    case OP_SBIT:
      {
	tic54x_symbol *sbit = str_hash_find (sbit_hash, operand->buf);
	int value = is_absolute (operand) ?
	  operand->exp.X_add_number : (sbit ? sbit->value : -1);
	int reg = 0;

	if (insn->opcount == 1)
	  {
	    if (!sbit)
	      {
		as_bad (_("A status register or status bit name is required"));
		return 0;
	      }
	    const tic54x_symbol *ovb_sbit = str_hash_find(sbit_hash, "ovb");
	    if (ovb_sbit && sbit > ovb_sbit)
	      reg = 1;
	  }
	if (value == -1)
	  {
	    as_bad (_("Unrecognized status bit \"%s\""), operand->buf);
	    return 0;
	  }
	insn->opcode[0].word |= value;
	insn->opcode[0].word |= (reg << 9);
	return 1;
      }
    case OP_N:
      {
	uint16_t status_reg_val;
	if (strcasecmp (operand->buf, "st0") == 0)
	  {
	    status_reg_val = 0;
	  }
	else if (strcasecmp (operand->buf, "st1") == 0)
	  {
	    status_reg_val = 1;
	  }
	else if (operand->exp.X_op == O_constant &&
		 (operand->exp.X_add_number == 0 || operand->exp.X_add_number == 1))
	  {
	    status_reg_val = (uint16_t) operand->exp.X_add_number;
	  }
	else
	  {
	    as_bad (_("Invalid status register \"%s\""), operand->buf);
	    return 0;
	  }
	insn->opcode[0].word |= (status_reg_val << 9);
	return 1;
      }
    case OP_k5:
      return encode_integer (insn, operand, 0, -16, 15, 0x1F);
    case OP_k3:
      return encode_integer (insn, operand, 0, 0, 7, 0x7);
    case OP_k9:
      return encode_integer (insn, operand, 0, 0, 0x1FF, 0x1FF);

    case OP_12:
      if (operand->exp.X_add_number != 1 && operand->exp.X_add_number != 2)
	{
	  as_bad (_("Operand \"%s\" out of range (use 1 or 2)"), operand->buf);
	  return 0;
	}
      insn->opcode[0].word |= (operand->exp.X_add_number - 1) << 9;
      return 1;

    default:
      return 0;
    }
}

static void
emit_insn (tic54x_insn *insn)
{
  int i;
  flagword flags = bfd_section_flags(now_seg) | SEC_CODE;

  if (!bfd_set_section_flags (now_seg, flags))
    {
      as_warn (_("error setting flags for section \"%s\": %s"),
               bfd_section_name (now_seg),
               bfd_errmsg (bfd_get_error ()));
    }

  for (i = 0; i < insn->words; i++)
    {
      int current_operand_size = (insn->opcode[i].unresolved &&
                                  insn->opcode[i].r_type == BFD_RELOC_TIC54X_23) ? 4 : 2;
      char *p = frag_more(current_operand_size);

      if (current_operand_size == 2)
        {
          md_number_to_chars(p, insn->opcode[i].word, 2);
        }
      else /* current_operand_size == 4 */
        {
          md_number_to_chars(p, (valueT)insn->opcode[i].word << 16, 4);
        }

      if (insn->opcode[i].unresolved)
        {
          fix_new_exp(frag_now,
                      p - frag_now->fr_literal,
                      insn->opcode[i].r_nchars,
                      &insn->opcode[i].addr_expr,
                      false,
                      insn->opcode[i].r_type);
        }
    }
}

/* Convert the operand strings into appropriate opcode values
   return the total number of words used by the instruction.  */

static int
build_insn (tic54x_insn *insn)
{
  const char * const sp_addr_prefix = "*sp (";
  const size_t sp_addr_prefix_len = sizeof(sp_addr_prefix) - 1;

  // Detect if the instruction uses lk addressing.
  // Only non-parallel instructions support lk addressing.
  if (!(insn->tm->flags & FL_PAR))
    {
      for (int i = 0; i < insn->opcount; ++i)
	{
	  // Check for specific memory operand types, presence of '(',
	  // and ensure it's not stack-relative addressing.
	  if ((OPTYPE(insn->operands[i].type) == OP_Smem ||
	       OPTYPE(insn->operands[i].type) == OP_Lmem ||
	       OPTYPE(insn->operands[i].type) == OP_Sind) &&
	      strchr(insn->operands[i].buf, '(') &&
	      strncasecmp(insn->operands[i].buf, sp_addr_prefix, sp_addr_prefix_len) != 0)
	    {
	      insn->is_lkaddr = 1;
	      insn->lkoperand = i;
	      break;
	    }
	}
    }

  // Calculate the total number of words for the instruction.
  insn->words = insn->tm->words + insn->is_lkaddr;

  // Assign the primary opcode.
  insn->opcode[0].word = insn->tm->opcode;

  // If extended instruction, assign the secondary opcode,
  // adjusting index if lk addressing is used.
  if (insn->tm->flags & FL_EXT)
    insn->opcode[1 + insn->is_lkaddr].word = insn->tm->opcode2;

  // Encode all primary operands.
  for (int i = 0; i < insn->opcount; ++i)
    {
      if (!encode_operand (insn, insn->operands[i].type, &insn->operands[i]))
	{
	  return 0; // Return 0 on encoding failure.
	}
    }

  // If parallel instruction, encode all parallel operands.
  if (insn->tm->flags & FL_PAR)
    {
      for (int i = 0; i < insn->paropcount; ++i)
	{
	  if (!encode_operand (insn, insn->paroperands[i].type, &insn->paroperands[i]))
	    {
	      return 0; // Return 0 on encoding failure.
	    }
	}
    }

  // Emit the fully built instruction.
  emit_insn (insn);

  // Return the total number of words in the instruction.
  return insn->words;
}

#include <string.h> // For strcasecmp
#include <stdbool.h> // For bool type if C99 or later

// The following types (tic54x_insn, tic54x_op, tic54x_tm, O_constant,
// OP_Xmem, OP_SHFT, OP_Smem, OP_SHIFT, OP_SRC, OP_lk, is_accumulator,
// is_type, OPTYPE) are assumed to be defined in external headers
// relevant to the project, as per the original code context.

// Helper function to check if an operand represents a zero constant.
// Assumes 'op' is a valid pointer to a tic54x_op structure.
static inline bool
is_operand_zero_constant(const tic54x_op *op)
{
  return op->exp.X_op == O_constant && op->exp.X_add_number == 0;
}

// Helper function to perform the common operand collapsing action.
// This function moves operand 2 to position 1 and reduces the operand count.
// It assumes the caller has already validated that 'insn' is not NULL and
// that insn->opcount is sufficient (e.g., at least 3) for this operation to be meaningful.
static inline void
perform_operand_collapse(tic54x_insn *insn)
{
  insn->operands[1] = insn->operands[2];
  insn->opcount = 2;
}

// Constants for instruction names to avoid magic strings and potential typos.
static const char *const INS_ADD_NAME = "add";
static const char *const INS_LD_NAME = "ld";
static const char *const INS_STH_NAME = "sth";
static const char *const INS_STL_NAME = "stl";
static const char *const INS_SUB_NAME = "sub";

static int
optimize_insn (tic54x_insn *insn)
{
  // Basic input validation to prevent crashes from NULL pointers.
  // This improves reliability and security.
  if (insn == NULL || insn->tm == NULL || insn->tm->name == NULL)
    {
      return 0; // Cannot optimize an invalid instruction.
    }

  // --- Common Accumulator Optimization (applies to ADD and SUB) ---
  // This logic checks if the last two operands are identical accumulators.
  // Factored out for maintainability.
  bool is_accumulator_optimization_condition_met =
      insn->opcount > 1
      && is_accumulator(&insn->operands[insn->opcount - 2])
      && is_accumulator(&insn->operands[insn->opcount - 1])
      && strcasecmp(insn->operands[insn->opcount - 2].buf,
                    insn->operands[insn->opcount - 1].buf) == 0;

  if (is_accumulator_optimization_condition_met)
    {
      // Apply only if the instruction is ADD or SUB.
      if (strcasecmp(insn->tm->name, INS_ADD_NAME) == 0 ||
          strcasecmp(insn->tm->name, INS_SUB_NAME) == 0)
      {
          --insn->opcount;
          insn->using_default_dst = 1;
          return 1;
      }
    }

  // --- Common Zero-Shift Operand Condition ---
  // This condition checks if the second operand (index 1) is a zero constant
  // and its template type is either OP_SHIFT or OP_SHFT.
  // Factored out for maintainability and to prevent redundant checks.
  bool op1_is_shift_or_shft_type_and_zero = false;
  if (insn->opcount >= 2) // Ensure operand[1] is accessible.
    {
      int op_type_1_template = OPTYPE(insn->tm->operand_types[1]);
      if ((op_type_1_template == OP_SHIFT || op_type_1_template == OP_SHFT) &&
          is_operand_zero_constant(&insn->operands[1]))
        {
          op1_is_shift_or_shft_type_and_zero = true;
        }
    }

  // --- Instruction-Specific Optimizations ---
  // Use if-else if structure to handle different instruction names.
  if (strcasecmp(insn->tm->name, INS_ADD_NAME) == 0)
    {
      // The accumulator optimization for ADD is handled above.
      // Second ADD optimization: collapse if Xmem/Smem and shift count is zero.
      if (insn->opcount >= 3) // Need at least 3 operands for collapse_operands_1_to_2.
        {
          int op_type_0_template = OPTYPE(insn->tm->operand_types[0]);
          int op_type_1_template = OPTYPE(insn->tm->operand_types[1]);

          // Condition 1 for ADD: operand 0 is Xmem, operand 1 template is SHFT, and it's a zero shift.
          bool cond_add_xmem_shft_zero =
              (op_type_0_template == OP_Xmem && op_type_1_template == OP_SHFT && op1_is_shift_or_shft_type_and_zero);

          // Condition 2 for ADD: operand 0 is Smem, operand 1 template is SHIFT, actual operand type is SHIFT,
          // it's a zero shift, and opcount is exactly 3.
          bool cond_add_smem_shift_zero =
              (op_type_0_template == OP_Smem && op_type_1_template == OP_SHIFT &&
               is_type(&insn->operands[1], OP_SHIFT) && // Original check for actual operand type.
               op1_is_shift_or_shft_type_and_zero &&
               insn->opcount == 3); // Specific opcount requirement from original logic.

          if (cond_add_xmem_shft_zero || cond_add_smem_shift_zero)
            {
              perform_operand_collapse(insn);
              return 1;
            }
        }
    }
  else if (strcasecmp(insn->tm->name, INS_LD_NAME) == 0)
    {
      if (insn->opcount == 3 && insn->operands[0].type != OP_SRC)
        {
          // LD optimization: applies if shift is zero and specific constraints on operand 0 are met.
          if (op1_is_shift_or_shft_type_and_zero)
            {
              int op_type_0_template = OPTYPE(insn->tm->operand_types[0]);

              bool cond_ld_lk_operand_constraint =
                  (op_type_0_template != OP_lk
                   || (insn->operands[0].exp.X_op == O_constant
                       && insn->operands[0].exp.X_add_number >= 0
                       && insn->operands[0].exp.X_add_number <= 255));

              if (cond_ld_lk_operand_constraint)
                {
                  perform_operand_collapse(insn);
                  return 1;
                }
            }
        }
    }
  else if (strcasecmp(insn->tm->name, INS_STH_NAME) == 0 ||
           strcasecmp(insn->tm->name, INS_STL_NAME) == 0)
    {
      // STH/STL optimization: collapse if shift is zero.
      // Requires at least 3 operands for collapse.
      if (insn->opcount >= 3 && op1_is_shift_or_shft_type_and_zero)
        {
          perform_operand_collapse(insn);
          return 1;
        }
    }
  else if (strcasecmp(insn->tm->name, INS_SUB_NAME) == 0)
    {
      // The accumulator optimization for SUB is handled above.
      // Second SUB optimization: collapse if Xmem/Smem and shift count is zero.
      if (insn->opcount == 3) // Specific opcount requirement from original logic.
        {
          int op_type_0_template = OPTYPE(insn->tm->operand_types[0]);
          int op_type_1_template = OPTYPE(insn->tm->operand_types[1]);

          // Check if operand 0 template is Smem and operand 1 template is SHIFT.
          bool cond_sub_smem_shift = (op_type_0_template == OP_Smem && op_type_1_template == OP_SHIFT);
          // Check if operand 0 template is Xmem and operand 1 template is SHFT.
          bool cond_sub_xmem_shft = (op_type_0_template == OP_Xmem && op_type_1_template == OP_SHFT);

          // If either condition is true and the shift is zero, perform collapse.
          if ((cond_sub_smem_shift || cond_sub_xmem_shft) && op1_is_shift_or_shft_type_and_zero)
            {
              perform_operand_collapse(insn);
              return 1;
            }
        }
    }

  return 0; // No optimization applied.
}

/* Find a matching template if possible, and get the operand strings.  */

static int
tic54x_parse_insn (tic54x_insn *insn, char *line)
{
  int optimized_and_retried;
  char *mnemonic_before_opt;

  insn->opcount = get_operands (insn->operands, line);
  if (insn->opcount < 0)
    {
      return 0;
    }

  do
    {
      optimized_and_retried = 0;
      mnemonic_before_opt = insn->mnemonic;

      tic54x_insn_type *tm_base_for_current_mnemonic = str_hash_find (op_hash, insn->mnemonic);
      if (!tm_base_for_current_mnemonic)
        {
          as_bad (_("Unrecognized instruction \"%s\""), insn->mnemonic);
          return 0;
        }

      tic54x_insn_type *current_variation_ptr = tm_base_for_current_mnemonic;

      while (current_variation_ptr->name
             && strcasecmp (current_variation_ptr->name, insn->mnemonic) == 0)
        {
          if (insn->opcount >= current_variation_ptr->minops
              && insn->opcount <= current_variation_ptr->maxops
              && operands_match (insn, &insn->operands[0], insn->opcount,
                                 current_variation_ptr->operand_types,
                                 current_variation_ptr->minops, current_variation_ptr->maxops))
            {
              insn->tm = current_variation_ptr;

              if (optimize_insn (insn))
                {
                  if (mnemonic_before_opt != insn->mnemonic
                      || strcmp(mnemonic_before_opt, insn->mnemonic) != 0)
                    {
                      optimized_and_retried = 1;
                      break;
                    }
                  return 1;
                }
              else
                {
                  return 1;
                }
            }
          ++current_variation_ptr;
        }
    } while (optimized_and_retried);

  as_bad (_("Unrecognized operand list '%s' for instruction '%s'"),
          line, insn->mnemonic);
  return 0;
}

/* We set this in start_line_hook, 'cause if we do a line replacement, we
   won't be able to see the next line.  */
static int parallel_on_next_line_hint = 0;

/* See if this is part of a parallel instruction
   Look for a subsequent line starting with "||".  */

static int
next_line_shows_parallel (char *next_line)
{
  /* Skip leading whitespace and statement terminators. */
  while (*next_line != '\0' &&
         (is_whitespace(*next_line) || is_end_of_stmt(*next_line)))
    {
      ++next_line;
    }

  /* After skipping, ensure there are at least two characters remaining
     to check for the parallel separator sequence. This prevents
     potential out-of-bounds access if the string is too short. */
  if (*next_line != '\0' && *(next_line + 1) != '\0')
    {
      return (next_line[0] == PARALLEL_SEPARATOR &&
              next_line[1] == PARALLEL_SEPARATOR);
    }
  else
    {
      /* Not enough characters for the parallel separator sequence. */
      return 0;
    }
}

static int
tic54x_parse_parallel_insn_firstline (tic54x_insn *insn, char *line)
{
  if (!insn || !insn->mnemonic || !line)
    {
      return 0;
    }

  insn->tm = str_hash_find (parop_hash, insn->mnemonic);
  if (!insn->tm)
    {
      as_bad (_("Unrecognized parallel instruction \"%s\""),
	      insn->mnemonic);
      return 0;
    }

  while (insn->tm->name && strcasecmp (insn->tm->name, insn->mnemonic) == 0)
    {
      insn->opcount = get_operands (insn->operands, line);
      if (insn->opcount < 0)
	{
	  return 0;
	}

      if (insn->opcount == 2)
	{
	  if (operands_match (insn, &insn->operands[0], insn->opcount,
			      insn->tm->operand_types, 2, 2))
	    {
	      return 1;
	    }
	}
      ++(insn->tm);
    }
  return 0;
}

/* Parse the second line of a two-line parallel instruction.  */

static int
tic54x_parse_parallel_insn_lastline (tic54x_insn *insn, char *line)
{
  if (insn == NULL || insn->tm == NULL || insn->mnemonic == NULL || insn->parmnemonic == NULL)
    {
      as_bad (_("Internal error: NULL instruction data for parallel instruction parsing."));
      return 0;
    }

  insn->paropcount = get_operands (insn->paroperands, line);

  const tic54x_tm_entry *template_iterator = insn->tm;
  int found_matching_mnemonic_pair = 0;

  while (template_iterator->name != NULL)
    {
      if (strcasecmp (template_iterator->name, insn->mnemonic) == 0)
        {
          if (template_iterator->parname != NULL && strcasecmp (template_iterator->parname, insn->parmnemonic) == 0)
            {
              found_matching_mnemonic_pair = 1;

              if (insn->paropcount >= template_iterator->minops &&
                  insn->paropcount <= template_iterator->maxops &&
                  operands_match (insn, insn->paroperands,
                                  insn->paropcount,
                                  template_iterator->paroperand_types,
                                  template_iterator->minops, template_iterator->maxops))
                {
                  return 1;
                }
            }
        }
      template_iterator++;
    }

  if (found_matching_mnemonic_pair)
    {
      as_bad (_("Invalid operand (s) for parallel instruction \"%s\""), insn->parmnemonic);
    }
  else
    {
      as_bad (_("Unrecognized parallel instruction combination \"%s || %s\""),
              insn->mnemonic, insn->parmnemonic);
    }

  return 0;
}

/* If quotes found, return copy of line up to closing quote;
   otherwise up until terminator.
   If it's a string, pass as-is; otherwise attempt substitution symbol
   replacement on the value.  */

static int
is_char_in_set (char c, const char *set)
{
  if (!set)
    return 0;

  for (const char *term_ptr = set; *term_ptr != '\0'; ++term_ptr)
    {
      if (c == *term_ptr)
        return 1;
    }
  return 0;
}

static char *
subsym_get_arg (char *line, const char *terminators, char **str, int nosub)
{
  char *ptr = line;
  char *endp = NULL;
  char *extracted_arg_allocated = NULL;
  *str = NULL;

  if (!line || !str)
    return NULL;

  int is_number_literal = ISDIGIT (*line);
  int is_quoted_string = (*line == '"');

  if (is_number_literal)
    {
      while (*ptr && ISDIGIT (*ptr))
	    {
	      ++ptr;
	    }
      endp = ptr;
      extracted_arg_allocated = xmemdup0 (line, ptr - line);
      if (!extracted_arg_allocated)
        return NULL;
    }
  else if (is_quoted_string)
    {
      char *saved_input_line_pointer = input_line_pointer;
      int len = 0;

      input_line_pointer = ptr;
      extracted_arg_allocated = demand_copy_C_string (&len);
      endp = input_line_pointer;
      input_line_pointer = saved_input_line_pointer;

      if (!extracted_arg_allocated)
        return NULL;

      if (!nosub && *extracted_arg_allocated == ':')
	    {
          char *substituted_str = subsym_substitute (extracted_arg_allocated, 1);
          free(extracted_arg_allocated);
          extracted_arg_allocated = substituted_str;
          if (!extracted_arg_allocated)
            return NULL;
	    }
    }
  else
    {
      char *start_ptr = ptr;
      while (*ptr && !is_char_in_set (*ptr, terminators))
	    {
	      ++ptr;
	    }
      endp = ptr;
      extracted_arg_allocated = xmemdup0 (start_ptr, ptr - start_ptr);
      if (!extracted_arg_allocated)
        return NULL;

      if (!nosub)
	    {
          subsym_ent_t *ent = subsym_lookup (extracted_arg_allocated, macro_level);
          if (ent && !ent->isproc)
            {
              free(extracted_arg_allocated);
              *str = ent->u.s;
              return endp;
            }
	    }
    }

  *str = extracted_arg_allocated;

  return endp;
}

/* Replace the given substitution string.
   We start at the innermost macro level, so that existing locals remain local
   Note: we're treating macro args identically to .var's; I don't know if
   that's compatible w/TI's assembler.  */

static void
subsym_create_or_replace (char *name, char *value)
{
  subsym_ent_t *ent = xmalloc (sizeof (*ent));

  ent->u.s = value;
  ent->freekey = 0;
  ent->freeval = 0;
  ent->isproc = 0;
  ent->ismath = 0;

  int target_level = 0;

  for (int i = macro_level; i > 0; i--)
    {
      if (str_hash_find (subsym_hash[i], name))
        {
          target_level = i;
          break;
        }
    }

  str_hash_insert (subsym_hash[target_level], name, ent, 1);
}

/* Look up the substitution string replacement for the given symbol.
   Start with the innermost macro substitution table given and work
   outwards.  */

static subsym_ent_t *
subsym_lookup (char *name, int nest_level)
{
  if (nest_level < 0)
    {
      return NULL;
    }

  for (int current_nest = nest_level; current_nest >= 0; --current_nest)
    {
      subsym_ent_t *value = (subsym_ent_t *)str_hash_find(subsym_hash[current_nest], name);

      if (value != NULL)
        {
          return value;
        }
    }

  return NULL;
}

/* Do substitution-symbol replacement on the given line (recursively).
   return the argument if no substitution was done

   Also look for built-in functions ($func (arg)) and local labels.

   If FORCED is set, look for forced substitutions of the form ':SYMBOL:'.  */

static char *
replace_substring_and_resize (char **buffer, char *start_segment,
                              char *end_segment, const char *replacement_value)
{
  size_t prefix_len = start_segment - *buffer;
  size_t replacement_len = strlen (replacement_value);
  size_t suffix_len = strlen (end_segment);
  size_t new_total_len = prefix_len + replacement_len + suffix_len;

  char *new_buffer = (char *) xmalloc (new_total_len + 1);
  if (!new_buffer)
    return NULL;

  memcpy (new_buffer, *buffer, prefix_len);
  memcpy (new_buffer + prefix_len, replacement_value, replacement_len);
  memcpy (new_buffer + prefix_len + replacement_len, end_segment, suffix_len + 1);

  char *new_segment_end_pos = new_buffer + prefix_len + replacement_len;

  free (*buffer);
  *buffer = new_buffer;

  return new_segment_end_pos;
}

static char *
extract_symbol_name (char *start_parse_ptr, char **next_char_in_buffer_ptr)
{
    char *saved_input_line_pointer = input_line_pointer;
    input_line_pointer = start_parse_ptr;

    char *symbol_start_for_get_name = start_parse_ptr;
    char char_after_name_from_get_name = get_symbol_name (&symbol_start_for_get_name);

    char *symbol_end_in_buffer = input_line_pointer;

    if (char_after_name_from_get_name == '?')
    {
        symbol_end_in_buffer++;
        input_line_pointer++;
    }

    size_t name_len = symbol_end_in_buffer - symbol_start_for_get_name;
    char *name_copy = XNEWVEC(char, name_len + 1);
    if (!name_copy) {
        input_line_pointer = saved_input_line_pointer;
        return NULL;
    }
    strncpy(name_copy, symbol_start_for_get_name, name_len);
    name_copy[name_len] = '\0';

    *next_char_in_buffer_ptr = input_line_pointer;
    input_line_pointer = saved_input_line_pointer;
    return name_copy;
}

static char *
perform_symbol_substitution_block (char **replacement_buf_ptr, char *current_ptr,
                                   int forced, int eval_symbol, int *changed_flag)
{
  char *original_segment_start = current_ptr;
  char *extracted_symbol_name = NULL;
  char *value_to_insert = NULL;
  char *tail_ptr_after_symbol = NULL;
  subsym_ent_t *ent = NULL;
  int recurse = 1;
  char *saved_global_input_line_pointer = input_line_pointer;

  if (forced) {
    current_ptr++;
  }

  extracted_symbol_name = extract_symbol_name (current_ptr, &tail_ptr_after_symbol);
  if (!extracted_symbol_name) {
    as_bad (_("Failed to extract symbol name"));
    *changed_flag = -1;
    goto cleanup;
  }

  if (str_hash_find (subsym_recurse_hash, extracted_symbol_name) == NULL)
    {
      ent = subsym_lookup (extracted_symbol_name, macro_level);
      if (ent && !ent->isproc) {
        value_to_insert = xstrdup(ent->u.s);
        if (!value_to_insert && ent->u.s) { // If ent->u.s is not NULL, xstrdup failed
          as_bad(_("Memory error during symbol lookup for '%s'"), extracted_symbol_name);
          *changed_flag = -1;
          goto cleanup;
        }
      }
    }
  else
    {
      as_warn (_("%s symbol recursion stopped at "
                 "second appearance of '%s'"),
               forced ? "Forced substitution" : "Substitution", extracted_symbol_name);
    }

  if (value_to_insert == NULL && ((*extracted_symbol_name == '$' && ISDIGIT (extracted_symbol_name[1]) && extracted_symbol_name[2] == '\0')
                                  || extracted_symbol_name[strlen (extracted_symbol_name) - 1] == '?'))
    {
      char *local_label_value = (char *) str_hash_find (local_label_hash[macro_level], extracted_symbol_name);
      if (local_label_value == NULL)
        {
          char digit_buf[11];
          char *temp_name_for_mod = xstrdup (extracted_symbol_name);
          if (!temp_name_for_mod) { as_bad(_("Memory error for temp local label name")); *changed_flag = -1; goto cleanup; }

          if (*temp_name_for_mod != '$')
            temp_name_for_mod[strlen (temp_name_for_mod) - 1] = '\0';
          sprintf (digit_buf, ".%d", local_label_id++);

          value_to_insert = XNEWVEC(char, strlen(temp_name_for_mod) + strlen(digit_buf) + 1);
          if (!value_to_insert) { as_bad(_("Memory error for new local label value")); free(temp_name_for_mod); *changed_flag = -1; goto cleanup; }
          strcpy (value_to_insert, temp_name_for_mod);
          strcat (value_to_insert, digit_buf);
          free (temp_name_for_mod);

          str_hash_insert (local_label_hash[macro_level], extracted_symbol_name, value_to_insert, 0);
        }
      else
        {
          value_to_insert = xstrdup(local_label_value);
          if (!value_to_insert) { as_bad(_("Memory error for existing local label value")); *changed_flag = -1; goto cleanup; }
        }
    }
  else if (ent != NULL && ent->isproc && *extracted_symbol_name == '$')
    {
      const subsym_proc_entry *entry = ent->u.p;
      char *arg1 = NULL, *arg2 = NULL;
      char *func_tail_ptr = NULL;
      char saved_char_at_tail = *tail_ptr_after_symbol;

      input_line_pointer = tail_ptr_after_symbol;

      if (*tail_ptr_after_symbol != '(')
        {
          as_bad (_("Missing '(' after substitution symbol function '%s'"), extracted_symbol_name);
          *changed_flag = -1; goto restore_global_input_ptr_and_cleanup;
        }
      input_line_pointer++;

      if (entry->ismath)
        {
          float farg1, farg2 = 0;
          farg1 = (float) strtod (input_line_pointer, &input_line_pointer);
          if (entry->nargs == 2)
            {
              if (*input_line_pointer++ != ',')
                { as_bad (_("Expecting second argument for math function '%s'"), extracted_symbol_name); *changed_flag = -1; goto restore_global_input_ptr_and_cleanup; }
              farg2 = (float) strtod (input_line_pointer, &input_line_pointer);
            }
          char val_buf[128];
          if (entry->type == 2)
            sprintf (val_buf, "%d", (*entry->proc.i) (farg1, farg2));
          else
            sprintf (val_buf, "%f", (*entry->proc.f) (farg1, farg2));
          value_to_insert = xstrdup(val_buf);
          if (!value_to_insert) { as_bad(_("Memory error for math function result")); *changed_flag = -1; goto restore_global_input_ptr_and_cleanup; }

          if (*input_line_pointer++ != ')')
            { as_bad (_("Extra junk in function call for '%s', expecting ')'"), extracted_symbol_name); free(value_to_insert); *changed_flag = -1; goto restore_global_input_ptr_and_cleanup; }
          recurse = 0;
        }
      else
        {
          int arg_type[2] = { 0, 0 };
          int ismember_func = !strcmp (entry->name, "$ismember");

          arg_type[0] = (*input_line_pointer == '"') ? 1 : 0;
          input_line_pointer = (char *)subsym_get_arg (input_line_pointer, ",)", &arg1, ismember_func);
          if (!input_line_pointer || (!arg1 && arg_type[0] != 0))
            { as_bad (_("Invalid first argument for function '%s'"), extracted_symbol_name); *changed_flag = -1; goto restore_global_input_ptr_and_cleanup; }

          if (entry->nargs == 2)
            {
              if (*input_line_pointer++ != ',')
                { as_bad (_("Function '%s' expects two arguments"), extracted_symbol_name); *changed_flag = -1; goto restore_global_input_ptr_and_cleanup; }
              arg_type[1] = (ISDIGIT (*input_line_pointer)) ? 2 : (*input_line_pointer == '"');
              input_line_pointer = (char *)subsym_get_arg (input_line_pointer, ")", &arg2, ismember_func);
              if (!input_line_pointer || (!arg2 && arg_type[1] != 2 && !ismember_func))
                { as_bad (_("Invalid second argument for function '%s'"), extracted_symbol_name); *changed_flag = -1; goto restore_global_input_ptr_and_cleanup; }
            }

          if ((!strcmp (entry->name, "$firstch") || !strcmp (entry->name, "$lastch")) && arg_type[1] != 2)
            { as_bad (_("Expecting character constant argument for function '%s'"), extracted_symbol_name); *changed_flag = -1; goto restore_global_input_ptr_and_cleanup; }
          if (ismember_func && (arg_type[0] != 0 || arg_type[1] != 0))
            { as_bad (_("Both arguments must be substitution symbols for '$ismember'")); *changed_flag = -1; goto restore_global_input_ptr_and_cleanup; }

          if (*input_line_pointer++ != ')')
            { as_bad (_("Extra junk in function call for '%s', expecting ')'"), extracted_symbol_name); *changed_flag = -1; goto restore_global_input_ptr_and_cleanup; }

          char val_buf[64];
          sprintf (val_buf, "%d", (*entry->proc.s) (arg1, arg2));
          value_to_insert = xstrdup(val_buf);
          if (!value_to_insert) { as_bad(_("Memory error for string function result")); *changed_flag = -1; goto restore_global_input_ptr_and_cleanup; }
        }
      func_tail_ptr = input_line_pointer;
      tail_ptr_after_symbol = func_tail_ptr;

    restore_global_input_ptr_and_cleanup:
      input_line_pointer = saved_global_input_line_pointer; // Always restore global
      if (*changed_flag == -1) {
        if (value_to_insert) free(value_to_insert);
        goto cleanup;
      }
    }

  if (value_to_insert != NULL && !eval_symbol)
    {
      if (recurse)
        {
          str_hash_insert (subsym_recurse_hash, extracted_symbol_name, extracted_symbol_name, 0);
          char *rec_value = subsym_substitute (value_to_insert, macro_level > 0);
          str_hash_delete (subsym_recurse_hash, extracted_symbol_name);
          free(value_to_insert);
          value_to_insert = rec_value;
        }

      if (forced && *tail_ptr_after_symbol == '(')
        {
          unsigned beg_idx = 0, len = 1;
          char *saved_tmp_global_input_ptr = input_line_pointer;
          input_line_pointer = tail_ptr_after_symbol + 1;

          beg_idx = get_absolute_expression ();
          if (beg_idx < 1) { as_bad (_("Invalid subscript (use 1 to %d)"), (int) strlen (value_to_insert)); input_line_pointer = saved_tmp_global_input_ptr; free(value_to_insert); *changed_flag = -1; goto cleanup; }

          if (*input_line_pointer == ',')
            {
              input_line_pointer++;
              len = get_absolute_expression ();
              if (beg_idx + len > strlen (value_to_insert) + 1)
                { as_bad (_("Invalid length (use 0 to %d)"), (int) strlen (value_to_insert) - beg_idx + 1); input_line_pointer = saved_tmp_global_input_ptr; free(value_to_insert); *changed_flag = -1; goto cleanup; }
            }
          if (*input_line_pointer++ != ')')
            { as_bad (_("Missing ')' in subscripted substitution symbol expression")); input_line_pointer = saved_tmp_global_input_ptr; free(value_to_insert); *changed_flag = -1; goto cleanup; }

          char *temp_sub_val_buf = xstrdup(value_to_insert);
          if (!temp_sub_val_buf) { as_bad(_("Memory error for subscripted value")); input_line_pointer = saved_tmp_global_input_ptr; free(value_to_insert); *changed_flag = -1; goto cleanup; }

          if (beg_idx - 1 + len > strlen(temp_sub_val_buf)) {
              len = strlen(temp_sub_val_buf) - (beg_idx - 1);
              if (len < 0) len = 0;
          }
          char *subscripted_segment = temp_sub_val_buf + (beg_idx - 1);
          subscripted_segment[len] = '\0';

          free(value_to_insert);
          value_to_insert = xstrdup(subscripted_segment);
          free(temp_sub_val_buf); // Free the xstrdup before pointer arithmetic
          if (!value_to_insert) { as_bad(_("Memory error for subscripted value copy")); input_line_pointer = saved_tmp_global_input_ptr; *changed_flag = -1; goto cleanup; }

          tail_ptr_after_symbol = input_line_pointer;
          input_line_pointer = saved_tmp_global_input_ptr;
        }

      char *new_current_ptr_pos = replace_substring_and_resize (replacement_buf_ptr, original_segment_start,
                                                                  tail_ptr_after_symbol, value_to_insert);
      free(value_to_insert);
      if (!new_current_ptr_pos) { as_bad(_("Memory error during replacement")); *changed_flag = -1; goto cleanup; }
      *changed_flag = 1;

      if (forced)
        {
          if (*new_current_ptr_pos != ':')
            { as_bad (_("Missing forced substitution terminator ':'")); *changed_flag = -1; goto cleanup; }
          new_current_ptr_pos++;
        }

      free(extracted_symbol_name);
      input_line_pointer = saved_global_input_line_pointer;
      return new_current_ptr_pos;
    }

  current_ptr = tail_ptr_after_symbol;

cleanup:
  if (extracted_symbol_name) free(extracted_symbol_name);
  if (value_to_insert) free(value_to_insert);
  input_line_pointer = saved_global_input_line_pointer;
  if (*changed_flag == -1) return NULL;
  return current_ptr;
}

static char *
subsym_substitute (char *line, int forced)
{
  char *replacement = xstrdup (line);
  if (!replacement)
    return line;

  char *current_ptr = replacement;
  int changed = 0; // 0: no change, 1: changed, -1: error occurred
  int line_conditional = 0;
  int eval_line = 0;
  ptrdiff_t eval_end_offset = -1;

  if (strstr (replacement, ".if") || strstr (replacement, ".elseif") || strstr (replacement, ".break"))
    line_conditional = 1;

  if (strstr (replacement, ".eval") || strstr (replacement, ".asg"))
    {
      eval_line = 1;
      char *comma_pos = strrchr (replacement, ',');
      if (comma_pos)
        eval_end_offset = comma_pos - replacement;
      else
        eval_end_offset = strlen(replacement);
    }

  if (strstr (replacement, ".macro"))
    {
      free (replacement);
      return line;
    }

  while (!is_end_of_stmt (*current_ptr))
    {
      char current_char = *current_ptr;
      int eval_symbol = 0;

      if (eval_line && eval_end_offset != -1 && (current_ptr - replacement >= eval_end_offset))
        eval_symbol = 1;

      if (current_char == '"' && current_ptr[1] == '"' && current_ptr[2] == '"')
        {
          current_ptr[1] = '\\';
          char *tmp = strstr (current_ptr + 2, "\"\"\"");
          if (tmp)
            tmp[0] = '\\';
          changed = 1;
        }
      else if (line_conditional && current_char == '=')
        {
          if (current_ptr[1] == '=')
            {
              current_ptr += 2;
              continue;
            }
          char *new_ptr = replace_substring_and_resize (&replacement, current_ptr, current_ptr + 1, "==");
          if (!new_ptr) { changed = -1; goto cleanup; }
          current_ptr = new_ptr;
          changed = 1;
          continue;
        }
      else if ((forced && current_char == ':') || (!forced && is_name_beginner (current_char)))
        {
          char *new_ptr = perform_symbol_substitution_block (&replacement, current_ptr,
                                                             forced, eval_symbol, &changed);
          if (changed == -1) goto cleanup;
          current_ptr = new_ptr;
          continue;
        }
      else
        {
          current_ptr++;
        }
    }

cleanup:
  if (changed == 1)
    return replacement;

  free (replacement);
  return line;
}

/* We use this to handle substitution symbols
   hijack input_line_pointer, replacing it with our substituted string.

   .sslist should enable listing the line after replacements are made...

   returns the new buffer limit.  */

#include <string.h>
#include <stdlib.h>
#include <ctype.h>

extern char *input_line_pointer;
extern int macro_level;
extern int parallel_on_next_line_hint;
extern int substitution_line;

extern char *xmemdup0 (const char *s, size_t len);
extern int is_end_of_stmt (char c);
extern int next_line_shows_parallel (const char *line);
extern char *subsym_substitute (char *line, int flag);
extern void input_scrub_insert_line (char *line);
extern int is_whitespace (char c);

static char *
clean_up_line (char *str)
{
  if (str == NULL)
    return NULL;

  size_t len = strlen(str);
  if (len == 0)
    return str;

  char *comment_start = strchr(str, ';');
  if (comment_start != NULL)
    {
      *comment_start = '\0';
      len = strlen(str);
      if (len == 0)
        return str;
    }

  char *current_end = str + len - 1;
  while (current_end >= str && is_whitespace(*current_end))
    {
      *current_end = '\0';
      current_end--;
    }

  char *current_start = str;
  while (*current_start != '\0' && is_whitespace(*current_start))
    current_start++;

  if (current_start != str)
    {
      memmove(str, current_start, strlen(current_start) + 1);
    }

  return str;
}

void
tic54x_start_line_hook (void)
{
  char *stmt_end_ptr;
  char *original_line_copy = NULL;
  char *current_string_ptr = NULL;

  stmt_end_ptr = input_line_pointer;
  while (*stmt_end_ptr != '\0' && !is_end_of_stmt (*stmt_end_ptr))
    stmt_end_ptr++;

  original_line_copy = xmemdup0 (input_line_pointer, stmt_end_ptr - input_line_pointer);
  if (original_line_copy == NULL)
    {
      substitution_line = 0;
      return;
    }
  
  parallel_on_next_line_hint = next_line_shows_parallel (stmt_end_ptr);

  current_string_ptr = original_line_copy;

  char *temp_sub_result = NULL;

  if (macro_level > 0)
    {
      temp_sub_result = subsym_substitute (current_string_ptr, 1);
      if (temp_sub_result != current_string_ptr)
        {
          current_string_ptr = temp_sub_result;
        }
    }

  temp_sub_result = subsym_substitute (current_string_ptr, 0);
  if (temp_sub_result != current_string_ptr)
    {
      if (current_string_ptr != original_line_copy)
        free (current_string_ptr);
      
      current_string_ptr = temp_sub_result;
    }

  if (current_string_ptr != original_line_copy)
    {
      clean_up_line (current_string_ptr);

      input_line_pointer = stmt_end_ptr;
      input_scrub_insert_line (current_string_ptr);
      
      free (current_string_ptr);
      free (original_line_copy);

      substitution_line = 1;
    }
  else
    {
      free (original_line_copy);
      substitution_line = 0;
    }
}

/* This is the guts of the machine-dependent assembler.  STR points to a
   machine dependent instruction.  This function is supposed to emit
   the frags/bytes it assembles to.  */
static int
check_and_update_delay_slots (int words, int *delay_slots_ptr, int is_parallel_context,
                              const struct tic54x_tm *tm)
{
  if (*delay_slots_ptr == 0)
    return 0;

  if (words > *delay_slots_ptr)
    {
      if (is_parallel_context)
        {
          as_bad (ngettext ("Instruction does not fit in available "
                            "delay slots (%d-word insn, %d slot left)",
                            "Instruction does not fit in available "
                            "delay slots (%d-word insn, %d slots left)",
                            *delay_slots_ptr),
                  words, *delay_slots_ptr);
        }
      else
        {
          as_warn (ngettext ("Instruction does not fit in available "
                             "delay slots (%d-word insn, %d slot left). "
                             "Resulting behavior is undefined.",
                             "Instruction does not fit in available "
                             "delay slots (%d-word insn, %d slots left). "
                             "Resulting behavior is undefined.",
                             *delay_slots_ptr),
                   words, *delay_slots_ptr);
        }
      *delay_slots_ptr = 0;
      return 1;
    }

  if (!is_parallel_context && (tm->flags & FL_BMASK))
    {
      as_warn (_("Instructions which cause PC discontinuity are not "
                 "allowed in a delay slot. "
                 "Resulting behavior is undefined."));
    }

  *delay_slots_ptr -= words;
  return 0;
}

static void
handle_repeat_slot (const struct tic54x_insn *insn_ptr, int *repeat_slot_ptr)
{
  if (*repeat_slot_ptr == 0)
    return;

  if (insn_ptr->tm->flags & FL_NR)
    {
      as_warn (_("'%s' is not repeatable. "
                 "Resulting behavior is undefined."),
               insn_ptr->tm->name);
    }
  else if (insn_ptr->is_lkaddr)
    {
      as_warn (_("Instructions using long offset modifiers or absolute "
                 "addresses are not repeatable. "
                 "Resulting behavior is undefined."));
    }
  *repeat_slot_ptr = 0;
}

void
md_assemble (char *line)
{
  static int repeat_slot = 0;
  static int delay_slots = 0;
  static int is_parallel = 0;
  static struct tic54x_insn insn;
  char *lptr;
  char *savedp = input_line_pointer;
  int c;
  char *original_line_start = line;

  input_line_pointer = line;
  c = get_symbol_name (&line);

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

  if (is_parallel)
    {
      is_parallel = 0;

      strncpy (insn.parmnemonic, line, sizeof (insn.parmnemonic) - 1);
      insn.parmnemonic[sizeof (insn.parmnemonic) - 1] = '\0';

      lptr = input_line_pointer;
      *lptr = c;
      input_line_pointer = savedp;

      if (tic54x_parse_parallel_insn_lastline (&insn, lptr))
	{
	  int words = build_insn (&insn);

	  if (check_and_update_delay_slots (words, &delay_slots, 1, insn.tm))
	    return;
	}
      return;
    }

  memset (&insn, 0, sizeof (insn));
  strncpy (insn.mnemonic, line, sizeof (insn.mnemonic) - 1);
  insn.mnemonic[sizeof (insn.mnemonic) - 1] = '\0';

  lptr = input_line_pointer;
  *lptr = c;
  input_line_pointer = savedp;

  if (strstr (original_line_start, "||") != NULL || parallel_on_next_line_hint)
    {
      char *tmp = strstr (original_line_start, "||");
      if (tmp != NULL)
	*tmp = '\0';

      if (tic54x_parse_parallel_insn_firstline (&insn, lptr))
	{
	  is_parallel = 1;
	  if (tmp != NULL)
	    {
	      while (is_whitespace (tmp[2]))
		++tmp;
	      md_assemble (tmp + 2);
	    }
	}
      else
	{
	  as_bad (_("Unrecognized parallel instruction '%s'"), original_line_start);
	}
      return;
    }

  if (tic54x_parse_insn (&insn, lptr))
    {
      int words;

      if ((insn.tm->flags & FL_LP)
	  && cpu != V545LP && cpu != V546LP)
	{
	  as_bad (_("Instruction '%s' requires an LP cpu version"),
		  insn.tm->name);
	  return;
	}
      if ((insn.tm->flags & FL_FAR)
	  && amode != far_mode)
	{
	  as_bad (_("Instruction '%s' requires far mode addressing"),
		  insn.tm->name);
	  return;
	}

      words = build_insn (&insn);

      if (check_and_update_delay_slots (words, &delay_slots, 0, insn.tm))
        return;

      handle_repeat_slot (&insn, &repeat_slot);

      if (insn.tm->flags & B_REPEAT)
	{
	  repeat_slot = 1;
	}
      if (insn.tm->flags & FL_DELAY)
	{
	  delay_slots = 2;
	}
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

      /* Ensure filename is a valid string pointer.
       * If as_where returns NULL (e.g., if it cannot determine the current location),
       * provide a safe default string. This prevents c_dot_file_symbol from
       * potentially dereferencing a NULL pointer, improving reliability. */
      if (filename == NULL)
        {
          filename = "<unknown>";
        }

      c_dot_file_symbol (filename);
    }
}

/* In order to get gas to ignore any | chars at the start of a line,
   this function returns true if a | is found in a line.
   This lets us process parallel instructions, which span two lines.  */

int
tic54x_unrecognized_line (int c)
{
  return (int)(c == PARALLEL_SEPARATOR);
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

#include <stdbool.h>

symbolS *
tic54x_undefined_symbol (char *name)
{
  tic54x_symbol *sym_with_value = NULL;
  bool is_predefined = false;

  str_hash_table *value_providing_hashes[] = {
    cc_hash,
    cc2_hash,
    cc3_hash,
    sbit_hash,
    reg_hash,
    mmreg_hash,
    NULL
  };

  for (int i = 0; value_providing_hashes[i] != NULL; ++i)
    {
      sym_with_value = str_hash_find (value_providing_hashes[i], name);
      if (sym_with_value != NULL)
        {
          is_predefined = true;
          break;
        }
    }

  if (!is_predefined)
    {
      if (str_hash_find (misc_symbol_hash, name) != NULL)
        {
          is_predefined = true;
        }
      else if (!strcasecmp (name, "a") || !strcasecmp (name, "b"))
        {
          is_predefined = true;
        }
    }

  if (is_predefined)
    {
      return symbol_new (name, reg_section, &zero_address_frag,
                         sym_with_value ? sym_with_value->value : 0);
    }

  return NULL;
}

/* Parse a name in an expression before the expression parser takes a stab at
   it.  */

int
tic54x_parse_name (char *name,
		   expressionS *expn)
{
  (void)name; /* Parameter is unused, but part of the API contract */
  (void)expn; /* Parameter is unused, but part of the API contract */
  return 0;
}

const char *
md_atof (int type, char *literalP, int *sizeP)
{
  const bool apply_big_word_float_storage_conversion = true;
  return ieee_md_atof (type, literalP, sizeP, apply_big_word_float_storage_conversion);
}

arelent *
tc_gen_reloc (asection *section, fixS *fixP)
{
  arelent *rel;
  bfd_reloc_code_real_type code = fixP->fx_r_type;
  asymbol *sym = symbol_get_bfdsym (fixP->fx_addsy);

  rel = notes_alloc (sizeof (arelent));
  if (rel == NULL)
    {
      return NULL;
    }

  rel->sym_ptr_ptr = notes_alloc (sizeof (asymbol *));
  if (rel->sym_ptr_ptr == NULL)
    {
      /*
       * If notes_alloc requires explicit freeing of 'rel' on a subsequent
       * allocation failure, a call to notes_free(rel) would be needed here.
       * Assuming notes_alloc manages this or terminates on failure,
       * or 'rel' cleanup is handled at a higher level.
       */
      return NULL;
    }
  *rel->sym_ptr_ptr = sym;

  /* Relocation address is a host byte offset. */
  rel->address = (fixP->fx_frag->fr_address + fixP->fx_where) / OCTETS_PER_BYTE;

  rel->howto = bfd_reloc_type_lookup (stdoutput, code);

  /* If the symbol name matches the section name, apply the bank adjustment. */
  if (strcmp (sym->name, section->name) == 0)
    {
      rel->howto += HOWTO_BANK;
    }

  if (rel->howto == NULL)
    {
      const char *sym_name = S_GET_NAME (fixP->fx_addsy);
      if (sym_name == NULL)
	{
	  sym_name = "<unknown>";
	}
      /* as_fatal is assumed to terminate the program, making the 'return NULL'
       * unreachable in practice, but it's included for completeness of the
       * function's contract. If as_fatal does not exit, explicit cleanup
       * of 'rel' and 'rel->sym_ptr_ptr' would be required here.
       */
      as_fatal ("Cannot generate relocation type for symbol %s, code %s",
		sym_name, bfd_get_reloc_code_name (code));
      return NULL;
    }

  return rel;
}

/* Handle cons expressions.  */

void
tic54x_cons_fix_new (fragS *frag, int where, int octets, expressionS *expn)
{
  bfd_reloc_code_real_type r_value;

  switch (octets)
    {
    case 2:
      r_value = BFD_RELOC_TIC54X_16_OF_23;
      break;
    case 4:
      if (emitting_long)
	r_value = BFD_RELOC_TIC54X_23;
      else
	r_value = BFD_RELOC_32;
      break;
    default:
      as_bad (_("Unsupported relocation size %d"), octets);
      r_value = BFD_RELOC_TIC54X_16_OF_23;
      break;
    }
  fix_new_exp (frag, where, octets, expn, 0, r_value);
}

/* Attempt to simplify or even eliminate a fixup.
   To indicate that a fixup has been eliminated, set fixP->fx_done.

   If fixp->fx_addsy is non-NULL, we'll have to generate a reloc entry.   */

#define TIC54X_MS7_OF_23_VAL_SHIFT 16
#define TIC54X_MS7_OF_23_VAL_MASK  0x7F

#define VALP_16BIT_RESULT_MASK     0xFFFF

#define TIC54X_PARTLS7_EXISTING_BITS_MASK 0xFF80
#define TIC54X_PARTLS7_NEW_VAL_MASK       0x7F
#define VALP_LS7_RESULT_MASK              0x7F

#define TIC54X_PARTMS9_EXISTING_BITS_MASK 0xFE00
#define TIC54X_PARTMS9_NEW_VAL_SHIFT      7

#define TIC54X_32BIT_EXISTING_BITS_MASK   0xFF800000

void
md_apply_fix (fixS *fixP, valueT *valP, segT seg ATTRIBUTE_UNUSED)
{
  char *buf = fixP->fx_where + fixP->fx_frag->fr_literal;
  valueT val = *valP;

  switch (fixP->fx_r_type)
    {
    default:
      as_fatal ("Bad relocation type: 0x%02x", fixP->fx_r_type);
      return;

    case BFD_RELOC_TIC54X_MS7_OF_23:
      val = (val >> TIC54X_MS7_OF_23_VAL_SHIFT) & TIC54X_MS7_OF_23_VAL_MASK;
    case BFD_RELOC_TIC54X_16_OF_23:
    case BFD_RELOC_16:
      bfd_put_16 (stdoutput, val, buf);
      *valP = val & VALP_16BIT_RESULT_MASK;
      break;

    case BFD_RELOC_TIC54X_PARTLS7:
      bfd_put_16 (stdoutput,
                  (bfd_get_16 (stdoutput, buf) & TIC54X_PARTLS7_EXISTING_BITS_MASK) | (val & TIC54X_PARTLS7_NEW_VAL_MASK),
                  buf);
      *valP = val & VALP_LS7_RESULT_MASK;
      break;

    case BFD_RELOC_TIC54X_PARTMS9:
      bfd_put_16 (stdoutput,
                  (bfd_get_16 (stdoutput, buf) & TIC54X_PARTMS9_EXISTING_BITS_MASK) | (val >> TIC54X_PARTMS9_NEW_VAL_SHIFT),
                  buf);
      break;

    case BFD_RELOC_32:
    case BFD_RELOC_TIC54X_23:
      bfd_put_32 (stdoutput,
                  (bfd_get_32 (stdoutput, buf) & TIC54X_32BIT_EXISTING_BITS_MASK) | val,
                  buf);
      break;
    }

  if (fixP->fx_addsy == NULL && fixP->fx_pcrel == 0)
    {
      fixP->fx_done = 1;
    }
}

/* This is our chance to record section alignment
   don't need to do anything here, since BFD does the proper encoding.  */

valueT
md_section_align (segT segment, valueT section_size)
{
  (void)segment;
  return section_size;
}

long
md_pcrel_from (fixS *fixP)
{
  (void)fixP;
  return 0;
}

/* Mostly little-endian, but longwords (4 octets) get MS word stored
   first.  */

#define SPECIAL_CASE_N 4
#define WORD_SIZE_BYTES 2
#define SHIFT_FOR_UPPER_WORD (WORD_SIZE_BYTES * 8)
#define WORD_MASK ((1U << SHIFT_FOR_UPPER_WORD) - 1)

void
tic54x_number_to_chars (char *buf, valueT val, int n)
{
  if (n != SPECIAL_CASE_N)
    {
      number_to_chars_littleendian (buf, val, n);
    }
  else
    {
      valueT upper_word = val >> SHIFT_FOR_UPPER_WORD;
      valueT lower_word = val & WORD_MASK;

      number_to_chars_littleendian (buf, upper_word, WORD_SIZE_BYTES);
      number_to_chars_littleendian (buf + WORD_SIZE_BYTES, lower_word, WORD_SIZE_BYTES);
    }
}

int
tic54x_estimate_size_before_relax (fragS *frag,
				   segT seg)
{
  (void)frag;
  (void)seg;
  return 0;
}

/* We use this to handle bit allocations which we couldn't handle before due
   to symbols being in different frags.  return number of octets added.  */

int
tic54x_relax_frag (fragS *frag, long stretch ATTRIBUTE_UNUSED)
{
  if (frag == NULL)
    {
      return 0;
    }

  symbolS *sym = frag->fr_symbol;
  int growth_delta_to_return = 0;

  if (sym == NULL)
    {
      return 0;
    }

  struct bit_info *bi = (struct bit_info *) frag->fr_opcode;

  if (symbol_get_frag (sym) != &zero_address_frag
      || S_IS_COMMON (sym)
      || !S_IS_DEFINED (sym))
    {
      as_bad_where (frag->fr_file, frag->fr_line,
                    _("non-absolute value used with .space/.bes"));
    }

  int requested_size_in_bits = S_GET_VALUE (sym);

  if (requested_size_in_bits < 0)
    {
      as_warn (_("negative value ignored in %s"),
               bi->type == TYPE_SPACE ? ".space" :
               bi->type == TYPE_BES ? ".bes" : ".field");
      frag->tc_frag_data = 0;
      frag->fr_fix = 0;
      frag->fr_symbol = NULL;
      frag->fr_opcode = NULL;
      free (bi);
      return 0;
    }

  int bit_offset_in_prev_frag = frag_bit_offset (frag_prev (frag, bi->seg), bi->seg);
  fragS *prev_frag = bit_offset_frag (frag_prev (frag, bi->seg), bi->seg);
  int available_bits_in_prev_word = 16 - bit_offset_in_prev_frag;

  if (bi->type == TYPE_FIELD)
    {
      if (bit_offset_in_prev_frag != 0 && available_bits_in_prev_word >= requested_size_in_bits)
        {
          char *p = prev_frag->fr_literal;
          valueT value = bi->value;

          value <<= (available_bits_in_prev_word - requested_size_in_bits);
          value |= (valueT)(((uint16_t)(unsigned char)p[1] << 8) | (uint16_t)(unsigned char)p[0]);

          md_number_to_chars (p, value, 2);

          if ((prev_frag->tc_frag_data += requested_size_in_bits) == 16)
            {
              prev_frag->tc_frag_data = 0;
            }
          if (bi->sym)
            {
              symbol_set_frag (bi->sym, prev_frag);
            }

          growth_delta_to_return = -frag->fr_fix;
          frag->fr_fix = 0;
          frag->tc_frag_data = 0;
        }
      else
        {
          char *p = frag->fr_literal;
          valueT value = bi->value << (16 - requested_size_in_bits);
          md_number_to_chars (p, value, 2);

          if ((frag->tc_frag_data = requested_size_in_bits) == 16)
            {
              frag->tc_frag_data = 0;
            }
          growth_delta_to_return = 0;
        }
    }
  else
    {
      bool frag_fully_absorbed_by_prev = false;
      int original_frag_fix_size_bytes = frag->fr_fix;

      if (bit_offset_in_prev_frag != 0 && bit_offset_in_prev_frag < 16)
        {
          if (available_bits_in_prev_word >= requested_size_in_bits)
            {
              prev_frag->tc_frag_data += requested_size_in_bits;
              if (prev_frag->tc_frag_data == 16)
                {
                  prev_frag->tc_frag_data = 0;
                }
              if (bi->sym)
                {
                  symbol_set_frag (bi->sym, prev_frag);
                }

              growth_delta_to_return = -original_frag_fix_size_bytes;
              frag->fr_fix = 0;
              frag->tc_frag_data = 0;
              frag_fully_absorbed_by_prev = true;
            }
          else
            {
              if (bi->type == TYPE_SPACE && bi->sym)
                {
                  symbol_set_frag (bi->sym, prev_frag);
                }
              requested_size_in_bits -= available_bits_in_prev_word;
            }
        }

      if (!frag_fully_absorbed_by_prev)
        {
          int new_total_frag_fix_size_bytes =
            (requested_size_in_bits + 15) / 16 * OCTETS_PER_BYTE;

          for (int i = 0; i < new_total_frag_fix_size_bytes; i++)
            {
              frag->fr_literal[i] = 0;
            }

          frag->fr_fix = new_total_frag_fix_size_bytes;
          frag->tc_frag_data = requested_size_in_bits % 16;

          if (bi->type == TYPE_BES && bi->sym)
            {
              S_SET_VALUE (bi->sym, frag->fr_fix / OCTETS_PER_BYTE - 1);
            }
          
          growth_delta_to_return = new_total_frag_fix_size_bytes - original_frag_fix_size_bytes;
        }
    }

  frag->fr_symbol = NULL;
  frag->fr_opcode = NULL;
  free (bi);

  return growth_delta_to_return;
}

void
tic54x_convert_frag (bfd *abfd ATTRIBUTE_UNUSED,
		     segT seg ATTRIBUTE_UNUSED,
		     fragS *frag)
{
  long numerator = (long) frag->fr_next->fr_address
                 - (long) frag->fr_address
                 - (long) frag->fr_fix;

  if (frag->fr_var <= 0)
    {
      as_bad_where (frag->fr_file, frag->fr_line,
		    _("invalid stride (fr_var=%ld) for .space/.bes operation; must be positive"),
		    (long) frag->fr_var);
      frag->fr_offset = 0;
    }
  else
    {
      frag->fr_offset = numerator / frag->fr_var;
      if (frag->fr_offset < 0)
	{
	  as_bad_where (frag->fr_file, frag->fr_line,
			_("attempt to .space/.bes backwards? (%ld)"),
			(long) frag->fr_offset);
	}
    }

  frag->fr_type = rs_space;
}

/* We need to avoid having labels defined for certain directives/pseudo-ops
   since once the label is defined, it's in the symbol table for good.  TI
   syntax puts the symbol *before* the pseudo (which is kinda like MRI syntax,
   I guess, except I've never seen a definition of MRI syntax).

   Don't allow labels to start with '.'  */

static int starts_with_directive_followed_by_space_or_eol(const char *s, const char *directive, size_t len) {
    if (s == NULL) {
        return 0;
    }

    if (strncasecmp(s, directive, len) == 0) {
        // If 's' starts with 'directive' (case-insensitive) for 'len' characters,
        // it implies 's' is at least 'len' characters long.
        // Thus, s[len] is a safe access, pointing to the character immediately after the directive
        // or the null terminator if 's' is exactly 'len' characters long.
        char char_after_directive = s[len];
        return (is_whitespace(char_after_directive) || char_after_directive == '\0');
    }
    return 0;
}

int
tic54x_start_label (const char * label_start, int nul_char, int next_char)
{
  const char *current_position;

  if (current_stag != NULL) {
    return 0;
  }

  // Disallow labels starting with "." unless it's explicitly allowed later or followed by ':'.
  // This check applies if the character after the label is NOT a colon.
  if (next_char != ':') {
    if (*label_start == '.') {
      as_bad (_("Invalid label '%s'"), label_start);
      return 0;
    }
  }

  if (is_end_of_stmt (next_char)) {
    return 1;
  }

  current_position = input_line_pointer;
  // If the character immediately following the label (nul_char) is a quote,
  // skip past the opening quote to process the rest of the line.
  if (nul_char == '"') {
    current_position++;
  }

  // Skip any whitespace characters that might follow the label
  while (is_whitespace (next_char)) {
    next_char = *++current_position;
  }

  // If the next significant character is not '.', it's a regular label, so it's valid.
  if (next_char != '.') {
    return 1;
  }

  // The character after the label is '.', so it might be a directive.
  // We need to determine if it's one of the directives that should NOT be treated as a label.
  // If it's any of these directives followed by whitespace or end-of-line,
  // then it's not considered a label.
  if (starts_with_directive_followed_by_space_or_eol(current_position, ".tag", 4) ||
      starts_with_directive_followed_by_space_or_eol(current_position, ".struct", 7) ||
      starts_with_directive_followed_by_space_or_eol(current_position, ".union", 6) ||
      starts_with_directive_followed_by_space_or_eol(current_position, ".macro", 6) ||
      starts_with_directive_followed_by_space_or_eol(current_position, ".set", 4) ||
      starts_with_directive_followed_by_space_or_eol(current_position, ".equ", 4)) {
    return 0; // It's a directive, not a label.
  }

  // If none of the above conditions determined it's not a label, then it is a label.
  return 1;
}
