#include "traversal.h"

/**
   \brief exit gracefully in case of error.
*/
void exitf(const char* message)
{
  fprintf(stderr,"BUG: %s.\n", message);
  exit(1);
}

/**
   \brief exit if unreachable code was reached.
*/
void unreachable()
{
  exitf("unreachable code was reached");
}

/**
   \brief Display a symbol in the given output stream.
*/
void visit_symbol(Z3_context c, FILE * out, Z3_symbol s)
{
  switch (Z3_get_symbol_kind(c, s)) {
  case Z3_INT_SYMBOL:
    fprintf(out, "#%d", Z3_get_symbol_int(c, s));
    break;
  case Z3_STRING_SYMBOL:
    fprintf(out, "%s", Z3_get_symbol_string(c, s));
    break;
  default:
    unreachable();
  }
}

/**
   \brief Display the given type.
*/
void visit_sort(Z3_context c, FILE * out, Z3_sort ty)
{
  switch (Z3_get_sort_kind(c, ty)) {
  case Z3_UNINTERPRETED_SORT:
    visit_symbol(c, out, Z3_get_sort_name(c, ty));
    break;
  case Z3_BOOL_SORT:
    fprintf(out, "bool");
    break;
  case Z3_INT_SORT:
    fprintf(out, "int");
    break;
  case Z3_REAL_SORT:
    fprintf(out, "real");
    break;
  case Z3_BV_SORT:
    fprintf(out, "bv%d", Z3_get_bv_sort_size(c, ty));
    break;
  case Z3_ARRAY_SORT:
    fprintf(out, "[");
    visit_sort(c, out, Z3_get_array_sort_domain(c, ty));
    fprintf(out, "->");
    visit_sort(c, out, Z3_get_array_sort_range(c, ty));
    fprintf(out, "]");
    break;
  case Z3_DATATYPE_SORT:
    if (Z3_get_datatype_sort_num_constructors(c, ty) != 1)
      {
	fprintf(out, "%s", Z3_sort_to_string(c,ty));
	break;
      }
    {
      unsigned num_fields = Z3_get_tuple_sort_num_fields(c, ty);
      unsigned i;
      fprintf(out, "(");
      for (i = 0; i < num_fields; i++) {
	Z3_func_decl field = Z3_get_tuple_sort_field_decl(c, ty, i);
	if (i > 0) {
	  fprintf(out, ", ");
	}
	visit_sort(c, out, Z3_get_range(c, field));
      }
      fprintf(out, ")");
      break;
    }
  default:
    fprintf(out, "unknown[");
    visit_symbol(c, out, Z3_get_sort_name(c, ty));
    fprintf(out, "]");
    break;
  }
}

/**
   \brief Custom ast pretty printer.

   This function demonstrates how to use the API to navigate terms.
*/
void visit(Z3_context c, FILE * out, Z3_ast v, std::set<int> & counter)
{
  switch (Z3_get_ast_kind(c, v)) {
  case Z3_NUMERAL_AST: {
    fprintf(out, "Application of %s\n", Z3_get_numeral_string(c, v));
    fprintf(out, "Id: %d\n", Z3_get_ast_id(c, v));
    counter.insert(Z3_get_ast_id(c, v));
    break;
  }
  case Z3_APP_AST: {
    unsigned i;
    Z3_app app = Z3_to_app(c, v);
    unsigned num_fields = Z3_get_app_num_args(c, app);
        
    for (i = 0; i < num_fields; i++)
      visit(c, out, Z3_get_app_arg(c, app, i), counter);

    //--------------------------------------------------
    // do something
    Z3_func_decl d = Z3_get_app_decl(c, app);
    fprintf(out, "Application of ");
    visit_symbol(c, out, Z3_get_decl_name(c, d));
    //fprintf(out, "%s", Z3_get_name(c, v));
    fprintf(out, "Id: %d \n", Z3_get_ast_id(c, v));
    //fprintf(out, " Hash: %d \n", Z3_get_ast_hash(c, v));
    counter.insert(Z3_get_ast_id(c, v));
    //--------------------------------------------------
	
    break;
  }
  case Z3_QUANTIFIER_AST: {
    fprintf(out, "quantifier\n");	
    fprintf(out, "Id: %d \n", Z3_get_ast_id(c, v));
    counter.insert(Z3_get_ast_id(c, v));
    break;
  }
  default:
    fprintf(out, "#unknown");
  }
}
