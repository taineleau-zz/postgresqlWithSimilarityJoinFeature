/*-------------------------------------------------------------------------
 *
 * funcapi.c
 *	  Utility and convenience functions for fmgr functions that return
 *	  sets and/or composite types.
 *
 * Copyright (c) 2002-2011, PostgreSQL Global Development Group
 *
 * IDENTIFICATION
 *	  src/backend/utils/fmgr/funcapi.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "access/heapam.h"
#include "catalog/namespace.h"
#include "catalog/pg_proc.h"
#include "catalog/pg_type.h"
#include "funcapi.h"
#include "nodes/nodeFuncs.h"
#include "parser/parse_coerce.h"
#include "utils/array.h"
#include "utils/builtins.h"
#include "utils/lsyscache.h"
#include "utils/memutils.h"
#include "utils/syscache.h"
#include "utils/typcache.h"

/*
 modification starts from here. ^_^
 by taineleau
 */

#include <string.h>
#include <stdlib.h>
#include <ctype.h>

#define length_t(x) VARSIZE((x)) - VARHDRSZ
#define CASTX(x, y) ((int)toupper(VARDATA((x))[(y)]))
#define shift2(x, y) (((x)%128) * 128 + (y)) // a little bit clumsy,  -_- too lazy to change it
#define min(a, b) ((a) < (b)? (a): (b))
#define max(a, b) ((a) > (b)? (a): (b))
int min3(int a, int b, int c) {return a < b?(a < c ? a : c):(b < c ? b : c);}


Datum jaccard_index(PG_FUNCTION_ARGS)
{
    /* Use a static integer array to record the elements of two sets. `1` stands for the set generated from str1 according to the jaccard_index rules, and `2` for str2.
       Use a `cleanclean` array to clean the records in order to speed up(avoid using memset to initialization).
       This version of implementation is slightly more efficient than the bitset method(cf. jackyyf's work), because the length of the given string are no greater than 100. ^o^
     */
    static int flag[65536];
    int cleanclean[233];
    text *str1 = (text *)PG_GETARG_TEXT_P(0);
    text *str2 = (text *)PG_GETARG_TEXT_P(1);
    int n = length_t(str1), m = length_t(str2), i, bg, cnt = 0, cnt_same = 0;
    float4 ans = .0;
    
    if (n != 0 && m != 0) {
        bg = CASTX(str1, 0);
        flag[bg] = 1;
        cleanclean[cnt++] = bg;
        for (i = 1; i < n; ++i) {
            bg = shift2(bg, CASTX(str1, i));
            if (!flag[bg]) {
                flag[bg] = 1;
                cleanclean[cnt++] = bg;
            }
        }
        
        bg %= 128;
        
        if (!flag[bg]) {
            flag[bg] = 1;
            cleanclean[cnt++] = bg;
        }
        
      // elog(LOG, "---debugdebugdebug--now %d", cnt);
        
        bg = CASTX(str2, 0);
        if (!flag[bg]) {
            cleanclean[cnt++] = bg;
        } else if (flag[bg] == 1){
            cnt_same++;
        }
        flag[bg] = 2;
        for (i = 1; i < m; ++i) {
            bg = shift2(bg, CASTX(str2, i));
            if (!flag[bg]) {
                cleanclean[cnt++] = bg;
                flag[bg] = 2;
            } else if (flag[bg] == 1) {
                flag[bg] = 2;
                cnt_same++;
            }
        }


        
        bg %= 128;
        
        if (!flag[bg]) {
            cleanclean[cnt++] = bg;
        } else if (flag[bg] == 1)
            cnt_same++;
        
      //  elog(LOG, "---debugdebugdebug--total %d, same %d", cnt, cnt_same);
        
        ans = (float4)cnt_same/(float4)cnt;
        
        for (i = 0; i < cnt; ++i)
            flag[cleanclean[i]] = 0;
       // elog(LOG, "debug ans%.5f", ans);
        
    }
    
    PG_RETURN_FLOAT4(ans);
}


Datum levenshtein_distance(PG_FUNCTION_ARGS)
{
    /*
     O(n * m) time complexity to calculate levenshtein_distance.
     */
    text *str_01 = (text *)PG_GETARG_TEXT_P(0);
    text *str_02 = (text *)PG_GETARG_TEXT_P(1);
    static int d[110][110];
    int n = length_t(str_01), m = length_t(str_02), i, j;
    for(i = 0; i <= n; ++i)
        d[i][0] = i;
    for(i = 1; i <= m; ++i)
        d[0][i] = i;
    for(i = 1; i <= n; ++i)
        for(j = 1; j <= m; ++ j)
            if (CASTX(str_01, i - 1) == CASTX(str_02, j - 1))
                d[i][j] = d[i - 1][j - 1];
            else
                d[i][j] = min3(d[i - 1][j], d[i][j - 1], d[i - 1][j - 1]) + 1;
    
    PG_RETURN_INT32(d[n][m]);
}



/*
 
 EN:
 an optimized solution(called Ukkonen's algorithm) for levenshtein_distance
 time complexity is reduced to O(min(n, m) * d), in which d stands for the given levenshtein_distance, n
 
 cf. http://www.cs.helsinki.fi/u/ukkonen/InfCont85.PDF or
 http://www.berghel.net/publications/asm/asm.pdf

 CN:
 編輯距離的優化版本(Ukkonen算法)，時間複雜度優化為O(n * d),其中d為給定的的編輯距離
 詳細證明請參考這兩篇陳年論文：http://www.cs.helsinki.fi/u/ukkonen/InfCont85.PDF 和
 http://www.berghel.net/publications/asm/asm.pdf
 或 我的實驗報告
 
 */


Datum levenshtein_distance_v2(PG_FUNCTION_ARGS)
{
    text *a = (text *)PG_GETARG_TEXT_P(0);
    text *b = (text *)PG_GETARG_TEXT_P(1);
    int upper = (int)PG_GETARG_INT32(2) - 1; //upper is the given levenshtein_distance d

    static int f[101][101];
    int n = length_t(a), m = length_t(b), i, j, LDv2_L, LDv2_R;
    
    if (abs(n - m) > upper) // since the real levenshtein_distance would not less than |n - m|
        PG_RETURN_BOOL(false);
    
    static int c[128]; // just a trick
    memset(c, 0, sizeof c);
    for (i = 0; i < n; ++i)
        ++c[CASTX(a, i)];
    for (i = 0; i < m; ++i)
        --c[CASTX(b, i)];
    int sumc = 0;
    for (i = 0; i < 128; ++i)
        sumc += abs(c[i]);
    if ((sumc + 1) / 2 > upper)
        PG_RETURN_BOOL(false);
    
    //initialization
    for (i = 0; i < n; ++i)
        f[i][0] = i;
    for (i = 1; i < m; ++i)
        f[0][i] = i;
    
    // i - j 属于 [n - m - upper / 2, upper / 2]
    // upper / 2 >= i - j >= n - m - upper / 2
    // upper / 2 - i >= -j >= n - m - upper / 2 - i
    // i - upper / 2 <= j <= i - (n - m - upper / 2)
    
    int LDv2_KL = -((upper - abs(n - m)) / 2);
    int LDv2_KR = (upper - abs(n - m)) / 2;
    if (n <= m)
        LDv2_KL += n - m;
    else
        LDv2_KR += n - m;
    
    for (i = 1; i <= n; ++i) {
        LDv2_L = max(1, i - LDv2_KR);
        LDv2_R = min(m, i - LDv2_KL);
        for (j = LDv2_L; j <= LDv2_R; ++j) {
            f[i][j] = f[i - 1][j - 1] + (CASTX(a, i - 1) == CASTX(b, j - 1) ? 0 : 1);
            if (LDv2_KL <= (i - 1) - j && (i - 1) - j <= LDv2_KR)
                f[i][j] = min(f[i][j], f[i - 1][j] + 1);
            if (LDv2_KL <= i - (j - 1) && i - (j - 1) <= LDv2_KR)
                f[i][j] = min(f[i][j], f[i][j - 1] + 1);
        }
    }
    
    PG_RETURN_BOOL(f[n][m] <= upper);
}


/*
 modification ends up here.^_^
 by taineleau
 */


static void shutdown_MultiFuncCall(Datum arg);
static TypeFuncClass internal_get_result_type(Oid funcid,
						 Node *call_expr,
						 ReturnSetInfo *rsinfo,
						 Oid *resultTypeId,
						 TupleDesc *resultTupleDesc);
static bool resolve_polymorphic_tupdesc(TupleDesc tupdesc,
							oidvector *declared_args,
							Node *call_expr);
static TypeFuncClass get_type_func_class(Oid typid);


/*
 * init_MultiFuncCall
 * Create an empty FuncCallContext data structure
 * and do some other basic Multi-function call setup
 * and error checking
 */
FuncCallContext *
init_MultiFuncCall(PG_FUNCTION_ARGS)
{
	FuncCallContext *retval;

	/*
	 * Bail if we're called in the wrong context
	 */
	if (fcinfo->resultinfo == NULL || !IsA(fcinfo->resultinfo, ReturnSetInfo))
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("set-valued function called in context that cannot accept a set")));

	if (fcinfo->flinfo->fn_extra == NULL)
	{
		/*
		 * First call
		 */
		ReturnSetInfo *rsi = (ReturnSetInfo *) fcinfo->resultinfo;
		MemoryContext multi_call_ctx;

		/*
		 * Create a suitably long-lived context to hold cross-call data
		 */
		multi_call_ctx = AllocSetContextCreate(fcinfo->flinfo->fn_mcxt,
											   "SRF multi-call context",
											   ALLOCSET_SMALL_MINSIZE,
											   ALLOCSET_SMALL_INITSIZE,
											   ALLOCSET_SMALL_MAXSIZE);

		/*
		 * Allocate suitably long-lived space and zero it
		 */
		retval = (FuncCallContext *)
			MemoryContextAllocZero(multi_call_ctx,
								   sizeof(FuncCallContext));

		/*
		 * initialize the elements
		 */
		retval->call_cntr = 0;
		retval->max_calls = 0;
		retval->slot = NULL;
		retval->user_fctx = NULL;
		retval->attinmeta = NULL;
		retval->tuple_desc = NULL;
		retval->multi_call_memory_ctx = multi_call_ctx;

		/*
		 * save the pointer for cross-call use
		 */
		fcinfo->flinfo->fn_extra = retval;

		/*
		 * Ensure we will get shut down cleanly if the exprcontext is not run
		 * to completion.
		 */
		RegisterExprContextCallback(rsi->econtext,
									shutdown_MultiFuncCall,
									PointerGetDatum(fcinfo->flinfo));
	}
	else
	{
		/* second and subsequent calls */
		elog(ERROR, "init_MultiFuncCall cannot be called more than once");

		/* never reached, but keep compiler happy */
		retval = NULL;
	}

	return retval;
}

/*
 * per_MultiFuncCall
 *
 * Do Multi-function per-call setup
 */
FuncCallContext *
per_MultiFuncCall(PG_FUNCTION_ARGS)
{
	FuncCallContext *retval = (FuncCallContext *) fcinfo->flinfo->fn_extra;

	/*
	 * Clear the TupleTableSlot, if present.  This is for safety's sake: the
	 * Slot will be in a long-lived context (it better be, if the
	 * FuncCallContext is pointing to it), but in most usage patterns the
	 * tuples stored in it will be in the function's per-tuple context. So at
	 * the beginning of each call, the Slot will hold a dangling pointer to an
	 * already-recycled tuple.	We clear it out here.
	 *
	 * Note: use of retval->slot is obsolete as of 8.0, and we expect that it
	 * will always be NULL.  This is just here for backwards compatibility in
	 * case someone creates a slot anyway.
	 */
	if (retval->slot != NULL)
		ExecClearTuple(retval->slot);

	return retval;
}

/*
 * end_MultiFuncCall
 * Clean up after init_MultiFuncCall
 */
void
end_MultiFuncCall(PG_FUNCTION_ARGS, FuncCallContext *funcctx)
{
	ReturnSetInfo *rsi = (ReturnSetInfo *) fcinfo->resultinfo;

	/* Deregister the shutdown callback */
	UnregisterExprContextCallback(rsi->econtext,
								  shutdown_MultiFuncCall,
								  PointerGetDatum(fcinfo->flinfo));

	/* But use it to do the real work */
	shutdown_MultiFuncCall(PointerGetDatum(fcinfo->flinfo));
}

/*
 * shutdown_MultiFuncCall
 * Shutdown function to clean up after init_MultiFuncCall
 */
static void
shutdown_MultiFuncCall(Datum arg)
{
	FmgrInfo   *flinfo = (FmgrInfo *) DatumGetPointer(arg);
	FuncCallContext *funcctx = (FuncCallContext *) flinfo->fn_extra;

	/* unbind from flinfo */
	flinfo->fn_extra = NULL;

	/*
	 * Delete context that holds all multi-call data, including the
	 * FuncCallContext itself
	 */
	MemoryContextDelete(funcctx->multi_call_memory_ctx);
}


/*
 * get_call_result_type
 *		Given a function's call info record, determine the kind of datatype
 *		it is supposed to return.  If resultTypeId isn't NULL, *resultTypeId
 *		receives the actual datatype OID (this is mainly useful for scalar
 *		result types).	If resultTupleDesc isn't NULL, *resultTupleDesc
 *		receives a pointer to a TupleDesc when the result is of a composite
 *		type, or NULL when it's a scalar result.
 *
 * One hard case that this handles is resolution of actual rowtypes for
 * functions returning RECORD (from either the function's OUT parameter
 * list, or a ReturnSetInfo context node).	TYPEFUNC_RECORD is returned
 * only when we couldn't resolve the actual rowtype for lack of information.
 *
 * The other hard case that this handles is resolution of polymorphism.
 * We will never return polymorphic pseudotypes (ANYELEMENT etc), either
 * as a scalar result type or as a component of a rowtype.
 *
 * This function is relatively expensive --- in a function returning set,
 * try to call it only the first time through.
 */
TypeFuncClass
get_call_result_type(FunctionCallInfo fcinfo,
					 Oid *resultTypeId,
					 TupleDesc *resultTupleDesc)
{
	return internal_get_result_type(fcinfo->flinfo->fn_oid,
									fcinfo->flinfo->fn_expr,
									(ReturnSetInfo *) fcinfo->resultinfo,
									resultTypeId,
									resultTupleDesc);
}

/*
 * get_expr_result_type
 *		As above, but work from a calling expression node tree
 */
TypeFuncClass
get_expr_result_type(Node *expr,
					 Oid *resultTypeId,
					 TupleDesc *resultTupleDesc)
{
	TypeFuncClass result;

	if (expr && IsA(expr, FuncExpr))
		result = internal_get_result_type(((FuncExpr *) expr)->funcid,
										  expr,
										  NULL,
										  resultTypeId,
										  resultTupleDesc);
	else if (expr && IsA(expr, OpExpr))
		result = internal_get_result_type(get_opcode(((OpExpr *) expr)->opno),
										  expr,
										  NULL,
										  resultTypeId,
										  resultTupleDesc);
	else
	{
		/* handle as a generic expression; no chance to resolve RECORD */
		Oid			typid = exprType(expr);

		if (resultTypeId)
			*resultTypeId = typid;
		if (resultTupleDesc)
			*resultTupleDesc = NULL;
		result = get_type_func_class(typid);
		if (result == TYPEFUNC_COMPOSITE && resultTupleDesc)
			*resultTupleDesc = lookup_rowtype_tupdesc_copy(typid, -1);
	}

	return result;
}

/*
 * get_func_result_type
 *		As above, but work from a function's OID only
 *
 * This will not be able to resolve pure-RECORD results nor polymorphism.
 */
TypeFuncClass
get_func_result_type(Oid functionId,
					 Oid *resultTypeId,
					 TupleDesc *resultTupleDesc)
{
	return internal_get_result_type(functionId,
									NULL,
									NULL,
									resultTypeId,
									resultTupleDesc);
}

/*
 * internal_get_result_type -- workhorse code implementing all the above
 *
 * funcid must always be supplied.	call_expr and rsinfo can be NULL if not
 * available.  We will return TYPEFUNC_RECORD, and store NULL into
 * *resultTupleDesc, if we cannot deduce the complete result rowtype from
 * the available information.
 */
static TypeFuncClass
internal_get_result_type(Oid funcid,
						 Node *call_expr,
						 ReturnSetInfo *rsinfo,
						 Oid *resultTypeId,
						 TupleDesc *resultTupleDesc)
{
	TypeFuncClass result;
	HeapTuple	tp;
	Form_pg_proc procform;
	Oid			rettype;
	TupleDesc	tupdesc;

	/* First fetch the function's pg_proc row to inspect its rettype */
	tp = SearchSysCache1(PROCOID, ObjectIdGetDatum(funcid));
	if (!HeapTupleIsValid(tp))
		elog(ERROR, "cache lookup failed for function %u", funcid);
	procform = (Form_pg_proc) GETSTRUCT(tp);

	rettype = procform->prorettype;

	/* Check for OUT parameters defining a RECORD result */
	tupdesc = build_function_result_tupdesc_t(tp);
	if (tupdesc)
	{
		/*
		 * It has OUT parameters, so it's basically like a regular composite
		 * type, except we have to be able to resolve any polymorphic OUT
		 * parameters.
		 */
		if (resultTypeId)
			*resultTypeId = rettype;

		if (resolve_polymorphic_tupdesc(tupdesc,
										&procform->proargtypes,
										call_expr))
		{
			if (tupdesc->tdtypeid == RECORDOID &&
				tupdesc->tdtypmod < 0)
				assign_record_type_typmod(tupdesc);
			if (resultTupleDesc)
				*resultTupleDesc = tupdesc;
			result = TYPEFUNC_COMPOSITE;
		}
		else
		{
			if (resultTupleDesc)
				*resultTupleDesc = NULL;
			result = TYPEFUNC_RECORD;
		}

		ReleaseSysCache(tp);

		return result;
	}

	/*
	 * If scalar polymorphic result, try to resolve it.
	 */
	if (IsPolymorphicType(rettype))
	{
		Oid			newrettype = exprType(call_expr);

		if (newrettype == InvalidOid)	/* this probably should not happen */
			ereport(ERROR,
					(errcode(ERRCODE_DATATYPE_MISMATCH),
					 errmsg("could not determine actual result type for function \"%s\" declared to return type %s",
							NameStr(procform->proname),
							format_type_be(rettype))));
		rettype = newrettype;
	}

	if (resultTypeId)
		*resultTypeId = rettype;
	if (resultTupleDesc)
		*resultTupleDesc = NULL;	/* default result */

	/* Classify the result type */
	result = get_type_func_class(rettype);
	switch (result)
	{
		case TYPEFUNC_COMPOSITE:
			if (resultTupleDesc)
				*resultTupleDesc = lookup_rowtype_tupdesc_copy(rettype, -1);
			/* Named composite types can't have any polymorphic columns */
			break;
		case TYPEFUNC_SCALAR:
			break;
		case TYPEFUNC_RECORD:
			/* We must get the tupledesc from call context */
			if (rsinfo && IsA(rsinfo, ReturnSetInfo) &&
				rsinfo->expectedDesc != NULL)
			{
				result = TYPEFUNC_COMPOSITE;
				if (resultTupleDesc)
					*resultTupleDesc = rsinfo->expectedDesc;
				/* Assume no polymorphic columns here, either */
			}
			break;
		default:
			break;
	}

	ReleaseSysCache(tp);

	return result;
}

/*
 * Given the result tuple descriptor for a function with OUT parameters,
 * replace any polymorphic columns (ANYELEMENT etc) with correct data types
 * deduced from the input arguments. Returns TRUE if able to deduce all types,
 * FALSE if not.
 */
static bool
resolve_polymorphic_tupdesc(TupleDesc tupdesc, oidvector *declared_args,
							Node *call_expr)
{
	int			natts = tupdesc->natts;
	int			nargs = declared_args->dim1;
	bool		have_anyelement_result = false;
	bool		have_anyarray_result = false;
	bool		have_anynonarray = false;
	bool		have_anyenum = false;
	Oid			anyelement_type = InvalidOid;
	Oid			anyarray_type = InvalidOid;
	Oid			anycollation;
	int			i;

	/* See if there are any polymorphic outputs; quick out if not */
	for (i = 0; i < natts; i++)
	{
		switch (tupdesc->attrs[i]->atttypid)
		{
			case ANYELEMENTOID:
				have_anyelement_result = true;
				break;
			case ANYARRAYOID:
				have_anyarray_result = true;
				break;
			case ANYNONARRAYOID:
				have_anyelement_result = true;
				have_anynonarray = true;
				break;
			case ANYENUMOID:
				have_anyelement_result = true;
				have_anyenum = true;
				break;
			default:
				break;
		}
	}
	if (!have_anyelement_result && !have_anyarray_result)
		return true;

	/*
	 * Otherwise, extract actual datatype(s) from input arguments.	(We assume
	 * the parser already validated consistency of the arguments.)
	 */
	if (!call_expr)
		return false;			/* no hope */

	for (i = 0; i < nargs; i++)
	{
		switch (declared_args->values[i])
		{
			case ANYELEMENTOID:
			case ANYNONARRAYOID:
			case ANYENUMOID:
				if (!OidIsValid(anyelement_type))
					anyelement_type = get_call_expr_argtype(call_expr, i);
				break;
			case ANYARRAYOID:
				if (!OidIsValid(anyarray_type))
					anyarray_type = get_call_expr_argtype(call_expr, i);
				break;
			default:
				break;
		}
	}

	/* If nothing found, parser messed up */
	if (!OidIsValid(anyelement_type) && !OidIsValid(anyarray_type))
		return false;

	/* If needed, deduce one polymorphic type from the other */
	if (have_anyelement_result && !OidIsValid(anyelement_type))
		anyelement_type = resolve_generic_type(ANYELEMENTOID,
											   anyarray_type,
											   ANYARRAYOID);
	if (have_anyarray_result && !OidIsValid(anyarray_type))
		anyarray_type = resolve_generic_type(ANYARRAYOID,
											 anyelement_type,
											 ANYELEMENTOID);

	/* Enforce ANYNONARRAY if needed */
	if (have_anynonarray && type_is_array(anyelement_type))
		return false;

	/* Enforce ANYENUM if needed */
	if (have_anyenum && !type_is_enum(anyelement_type))
		return false;

	/*
	 * Identify the collation to use for polymorphic OUT parameters. (It'll
	 * necessarily be the same for both anyelement and anyarray.)
	 */
	anycollation = get_typcollation(OidIsValid(anyelement_type) ? anyelement_type : anyarray_type);
	if (OidIsValid(anycollation))
	{
		/*
		 * The types are collatable, so consider whether to use a nondefault
		 * collation.  We do so if we can identify the input collation used
		 * for the function.
		 */
		Oid			inputcollation = exprInputCollation(call_expr);

		if (OidIsValid(inputcollation))
			anycollation = inputcollation;
	}

	/* And finally replace the tuple column types as needed */
	for (i = 0; i < natts; i++)
	{
		switch (tupdesc->attrs[i]->atttypid)
		{
			case ANYELEMENTOID:
			case ANYNONARRAYOID:
			case ANYENUMOID:
				TupleDescInitEntry(tupdesc, i + 1,
								   NameStr(tupdesc->attrs[i]->attname),
								   anyelement_type,
								   -1,
								   0);
				TupleDescInitEntryCollation(tupdesc, i + 1, anycollation);
				break;
			case ANYARRAYOID:
				TupleDescInitEntry(tupdesc, i + 1,
								   NameStr(tupdesc->attrs[i]->attname),
								   anyarray_type,
								   -1,
								   0);
				TupleDescInitEntryCollation(tupdesc, i + 1, anycollation);
				break;
			default:
				break;
		}
	}

	return true;
}

/*
 * Given the declared argument types and modes for a function, replace any
 * polymorphic types (ANYELEMENT etc) with correct data types deduced from the
 * input arguments.  Returns TRUE if able to deduce all types, FALSE if not.
 * This is the same logic as resolve_polymorphic_tupdesc, but with a different
 * argument representation.
 *
 * argmodes may be NULL, in which case all arguments are assumed to be IN mode.
 */
bool
resolve_polymorphic_argtypes(int numargs, Oid *argtypes, char *argmodes,
							 Node *call_expr)
{
	bool		have_anyelement_result = false;
	bool		have_anyarray_result = false;
	Oid			anyelement_type = InvalidOid;
	Oid			anyarray_type = InvalidOid;
	int			inargno;
	int			i;

	/* First pass: resolve polymorphic inputs, check for outputs */
	inargno = 0;
	for (i = 0; i < numargs; i++)
	{
		char		argmode = argmodes ? argmodes[i] : PROARGMODE_IN;

		switch (argtypes[i])
		{
			case ANYELEMENTOID:
			case ANYNONARRAYOID:
			case ANYENUMOID:
				if (argmode == PROARGMODE_OUT || argmode == PROARGMODE_TABLE)
					have_anyelement_result = true;
				else
				{
					if (!OidIsValid(anyelement_type))
					{
						anyelement_type = get_call_expr_argtype(call_expr,
																inargno);
						if (!OidIsValid(anyelement_type))
							return false;
					}
					argtypes[i] = anyelement_type;
				}
				break;
			case ANYARRAYOID:
				if (argmode == PROARGMODE_OUT || argmode == PROARGMODE_TABLE)
					have_anyarray_result = true;
				else
				{
					if (!OidIsValid(anyarray_type))
					{
						anyarray_type = get_call_expr_argtype(call_expr,
															  inargno);
						if (!OidIsValid(anyarray_type))
							return false;
					}
					argtypes[i] = anyarray_type;
				}
				break;
			default:
				break;
		}
		if (argmode != PROARGMODE_OUT && argmode != PROARGMODE_TABLE)
			inargno++;
	}

	/* Done? */
	if (!have_anyelement_result && !have_anyarray_result)
		return true;

	/* If no input polymorphics, parser messed up */
	if (!OidIsValid(anyelement_type) && !OidIsValid(anyarray_type))
		return false;

	/* If needed, deduce one polymorphic type from the other */
	if (have_anyelement_result && !OidIsValid(anyelement_type))
		anyelement_type = resolve_generic_type(ANYELEMENTOID,
											   anyarray_type,
											   ANYARRAYOID);
	if (have_anyarray_result && !OidIsValid(anyarray_type))
		anyarray_type = resolve_generic_type(ANYARRAYOID,
											 anyelement_type,
											 ANYELEMENTOID);

	/* XXX do we need to enforce ANYNONARRAY or ANYENUM here?  I think not */

	/* And finally replace the output column types as needed */
	for (i = 0; i < numargs; i++)
	{
		switch (argtypes[i])
		{
			case ANYELEMENTOID:
			case ANYNONARRAYOID:
			case ANYENUMOID:
				argtypes[i] = anyelement_type;
				break;
			case ANYARRAYOID:
				argtypes[i] = anyarray_type;
				break;
			default:
				break;
		}
	}

	return true;
}

/*
 * get_type_func_class
 *		Given the type OID, obtain its TYPEFUNC classification.
 *
 * This is intended to centralize a bunch of formerly ad-hoc code for
 * classifying types.  The categories used here are useful for deciding
 * how to handle functions returning the datatype.
 */
static TypeFuncClass
get_type_func_class(Oid typid)
{
	switch (get_typtype(typid))
	{
		case TYPTYPE_COMPOSITE:
			return TYPEFUNC_COMPOSITE;
		case TYPTYPE_BASE:
		case TYPTYPE_DOMAIN:
		case TYPTYPE_ENUM:
			return TYPEFUNC_SCALAR;
		case TYPTYPE_PSEUDO:
			if (typid == RECORDOID)
				return TYPEFUNC_RECORD;

			/*
			 * We treat VOID and CSTRING as legitimate scalar datatypes,
			 * mostly for the convenience of the JDBC driver (which wants to
			 * be able to do "SELECT * FROM foo()" for all legitimately
			 * user-callable functions).
			 */
			if (typid == VOIDOID || typid == CSTRINGOID)
				return TYPEFUNC_SCALAR;
			return TYPEFUNC_OTHER;
	}
	/* shouldn't get here, probably */
	return TYPEFUNC_OTHER;
}


/*
 * get_func_arg_info
 *
 * Fetch info about the argument types, names, and IN/OUT modes from the
 * pg_proc tuple.  Return value is the total number of arguments.
 * Other results are palloc'd.  *p_argtypes is always filled in, but
 * *p_argnames and *p_argmodes will be set NULL in the default cases
 * (no names, and all IN arguments, respectively).
 *
 * Note that this function simply fetches what is in the pg_proc tuple;
 * it doesn't do any interpretation of polymorphic types.
 */
int
get_func_arg_info(HeapTuple procTup,
				  Oid **p_argtypes, char ***p_argnames, char **p_argmodes)
{
	Form_pg_proc procStruct = (Form_pg_proc) GETSTRUCT(procTup);
	Datum		proallargtypes;
	Datum		proargmodes;
	Datum		proargnames;
	bool		isNull;
	ArrayType  *arr;
	int			numargs;
	Datum	   *elems;
	int			nelems;
	int			i;

	/* First discover the total number of parameters and get their types */
	proallargtypes = SysCacheGetAttr(PROCOID, procTup,
									 Anum_pg_proc_proallargtypes,
									 &isNull);
	if (!isNull)
	{
		/*
		 * We expect the arrays to be 1-D arrays of the right types; verify
		 * that.  For the OID and char arrays, we don't need to use
		 * deconstruct_array() since the array data is just going to look like
		 * a C array of values.
		 */
		arr = DatumGetArrayTypeP(proallargtypes);		/* ensure not toasted */
		numargs = ARR_DIMS(arr)[0];
		if (ARR_NDIM(arr) != 1 ||
			numargs < 0 ||
			ARR_HASNULL(arr) ||
			ARR_ELEMTYPE(arr) != OIDOID)
			elog(ERROR, "proallargtypes is not a 1-D Oid array");
		Assert(numargs >= procStruct->pronargs);
		*p_argtypes = (Oid *) palloc(numargs * sizeof(Oid));
		memcpy(*p_argtypes, ARR_DATA_PTR(arr),
			   numargs * sizeof(Oid));
	}
	else
	{
		/* If no proallargtypes, use proargtypes */
		numargs = procStruct->proargtypes.dim1;
		Assert(numargs == procStruct->pronargs);
		*p_argtypes = (Oid *) palloc(numargs * sizeof(Oid));
		memcpy(*p_argtypes, procStruct->proargtypes.values,
			   numargs * sizeof(Oid));
	}

	/* Get argument names, if available */
	proargnames = SysCacheGetAttr(PROCOID, procTup,
								  Anum_pg_proc_proargnames,
								  &isNull);
	if (isNull)
		*p_argnames = NULL;
	else
	{
		deconstruct_array(DatumGetArrayTypeP(proargnames),
						  TEXTOID, -1, false, 'i',
						  &elems, NULL, &nelems);
		if (nelems != numargs)	/* should not happen */
			elog(ERROR, "proargnames must have the same number of elements as the function has arguments");
		*p_argnames = (char **) palloc(sizeof(char *) * numargs);
		for (i = 0; i < numargs; i++)
			(*p_argnames)[i] = TextDatumGetCString(elems[i]);
	}

	/* Get argument modes, if available */
	proargmodes = SysCacheGetAttr(PROCOID, procTup,
								  Anum_pg_proc_proargmodes,
								  &isNull);
	if (isNull)
		*p_argmodes = NULL;
	else
	{
		arr = DatumGetArrayTypeP(proargmodes);	/* ensure not toasted */
		if (ARR_NDIM(arr) != 1 ||
			ARR_DIMS(arr)[0] != numargs ||
			ARR_HASNULL(arr) ||
			ARR_ELEMTYPE(arr) != CHAROID)
			elog(ERROR, "proargmodes is not a 1-D char array");
		*p_argmodes = (char *) palloc(numargs * sizeof(char));
		memcpy(*p_argmodes, ARR_DATA_PTR(arr),
			   numargs * sizeof(char));
	}

	return numargs;
}


/*
 * get_func_input_arg_names
 *
 * Extract the names of input arguments only, given a function's
 * proargnames and proargmodes entries in Datum form.
 *
 * Returns the number of input arguments, which is the length of the
 * palloc'd array returned to *arg_names.  Entries for unnamed args
 * are set to NULL.  You don't get anything if proargnames is NULL.
 */
int
get_func_input_arg_names(Datum proargnames, Datum proargmodes,
						 char ***arg_names)
{
	ArrayType  *arr;
	int			numargs;
	Datum	   *argnames;
	char	   *argmodes;
	char	  **inargnames;
	int			numinargs;
	int			i;

	/* Do nothing if null proargnames */
	if (proargnames == PointerGetDatum(NULL))
	{
		*arg_names = NULL;
		return 0;
	}

	/*
	 * We expect the arrays to be 1-D arrays of the right types; verify that.
	 * For proargmodes, we don't need to use deconstruct_array() since the
	 * array data is just going to look like a C array of values.
	 */
	arr = DatumGetArrayTypeP(proargnames);		/* ensure not toasted */
	if (ARR_NDIM(arr) != 1 ||
		ARR_HASNULL(arr) ||
		ARR_ELEMTYPE(arr) != TEXTOID)
		elog(ERROR, "proargnames is not a 1-D text array");
	deconstruct_array(arr, TEXTOID, -1, false, 'i',
					  &argnames, NULL, &numargs);
	if (proargmodes != PointerGetDatum(NULL))
	{
		arr = DatumGetArrayTypeP(proargmodes);	/* ensure not toasted */
		if (ARR_NDIM(arr) != 1 ||
			ARR_DIMS(arr)[0] != numargs ||
			ARR_HASNULL(arr) ||
			ARR_ELEMTYPE(arr) != CHAROID)
			elog(ERROR, "proargmodes is not a 1-D char array");
		argmodes = (char *) ARR_DATA_PTR(arr);
	}
	else
		argmodes = NULL;

	/* zero elements probably shouldn't happen, but handle it gracefully */
	if (numargs <= 0)
	{
		*arg_names = NULL;
		return 0;
	}

	/* extract input-argument names */
	inargnames = (char **) palloc(numargs * sizeof(char *));
	numinargs = 0;
	for (i = 0; i < numargs; i++)
	{
		if (argmodes == NULL ||
			argmodes[i] == PROARGMODE_IN ||
			argmodes[i] == PROARGMODE_INOUT ||
			argmodes[i] == PROARGMODE_VARIADIC)
		{
			char	   *pname = TextDatumGetCString(argnames[i]);

			if (pname[0] != '\0')
				inargnames[numinargs] = pname;
			else
				inargnames[numinargs] = NULL;
			numinargs++;
		}
	}

	*arg_names = inargnames;
	return numinargs;
}


/*
 * get_func_result_name
 *
 * If the function has exactly one output parameter, and that parameter
 * is named, return the name (as a palloc'd string).  Else return NULL.
 *
 * This is used to determine the default output column name for functions
 * returning scalar types.
 */
char *
get_func_result_name(Oid functionId)
{
	char	   *result;
	HeapTuple	procTuple;
	Datum		proargmodes;
	Datum		proargnames;
	bool		isnull;
	ArrayType  *arr;
	int			numargs;
	char	   *argmodes;
	Datum	   *argnames;
	int			numoutargs;
	int			nargnames;
	int			i;

	/* First fetch the function's pg_proc row */
	procTuple = SearchSysCache1(PROCOID, ObjectIdGetDatum(functionId));
	if (!HeapTupleIsValid(procTuple))
		elog(ERROR, "cache lookup failed for function %u", functionId);

	/* If there are no named OUT parameters, return NULL */
	if (heap_attisnull(procTuple, Anum_pg_proc_proargmodes) ||
		heap_attisnull(procTuple, Anum_pg_proc_proargnames))
		result = NULL;
	else
	{
		/* Get the data out of the tuple */
		proargmodes = SysCacheGetAttr(PROCOID, procTuple,
									  Anum_pg_proc_proargmodes,
									  &isnull);
		Assert(!isnull);
		proargnames = SysCacheGetAttr(PROCOID, procTuple,
									  Anum_pg_proc_proargnames,
									  &isnull);
		Assert(!isnull);

		/*
		 * We expect the arrays to be 1-D arrays of the right types; verify
		 * that.  For the char array, we don't need to use deconstruct_array()
		 * since the array data is just going to look like a C array of
		 * values.
		 */
		arr = DatumGetArrayTypeP(proargmodes);	/* ensure not toasted */
		numargs = ARR_DIMS(arr)[0];
		if (ARR_NDIM(arr) != 1 ||
			numargs < 0 ||
			ARR_HASNULL(arr) ||
			ARR_ELEMTYPE(arr) != CHAROID)
			elog(ERROR, "proargmodes is not a 1-D char array");
		argmodes = (char *) ARR_DATA_PTR(arr);
		arr = DatumGetArrayTypeP(proargnames);	/* ensure not toasted */
		if (ARR_NDIM(arr) != 1 ||
			ARR_DIMS(arr)[0] != numargs ||
			ARR_HASNULL(arr) ||
			ARR_ELEMTYPE(arr) != TEXTOID)
			elog(ERROR, "proargnames is not a 1-D text array");
		deconstruct_array(arr, TEXTOID, -1, false, 'i',
						  &argnames, NULL, &nargnames);
		Assert(nargnames == numargs);

		/* scan for output argument(s) */
		result = NULL;
		numoutargs = 0;
		for (i = 0; i < numargs; i++)
		{
			if (argmodes[i] == PROARGMODE_IN ||
				argmodes[i] == PROARGMODE_VARIADIC)
				continue;
			Assert(argmodes[i] == PROARGMODE_OUT ||
				   argmodes[i] == PROARGMODE_INOUT ||
				   argmodes[i] == PROARGMODE_TABLE);
			if (++numoutargs > 1)
			{
				/* multiple out args, so forget it */
				result = NULL;
				break;
			}
			result = TextDatumGetCString(argnames[i]);
			if (result == NULL || result[0] == '\0')
			{
				/* Parameter is not named, so forget it */
				result = NULL;
				break;
			}
		}
	}

	ReleaseSysCache(procTuple);

	return result;
}


/*
 * build_function_result_tupdesc_t
 *
 * Given a pg_proc row for a function, return a tuple descriptor for the
 * result rowtype, or NULL if the function does not have OUT parameters.
 *
 * Note that this does not handle resolution of polymorphic types;
 * that is deliberate.
 */
TupleDesc
build_function_result_tupdesc_t(HeapTuple procTuple)
{
	Form_pg_proc procform = (Form_pg_proc) GETSTRUCT(procTuple);
	Datum		proallargtypes;
	Datum		proargmodes;
	Datum		proargnames;
	bool		isnull;

	/* Return NULL if the function isn't declared to return RECORD */
	if (procform->prorettype != RECORDOID)
		return NULL;

	/* If there are no OUT parameters, return NULL */
	if (heap_attisnull(procTuple, Anum_pg_proc_proallargtypes) ||
		heap_attisnull(procTuple, Anum_pg_proc_proargmodes))
		return NULL;

	/* Get the data out of the tuple */
	proallargtypes = SysCacheGetAttr(PROCOID, procTuple,
									 Anum_pg_proc_proallargtypes,
									 &isnull);
	Assert(!isnull);
	proargmodes = SysCacheGetAttr(PROCOID, procTuple,
								  Anum_pg_proc_proargmodes,
								  &isnull);
	Assert(!isnull);
	proargnames = SysCacheGetAttr(PROCOID, procTuple,
								  Anum_pg_proc_proargnames,
								  &isnull);
	if (isnull)
		proargnames = PointerGetDatum(NULL);	/* just to be sure */

	return build_function_result_tupdesc_d(proallargtypes,
										   proargmodes,
										   proargnames);
}

/*
 * build_function_result_tupdesc_d
 *
 * Build a RECORD function's tupledesc from the pg_proc proallargtypes,
 * proargmodes, and proargnames arrays.  This is split out for the
 * convenience of ProcedureCreate, which needs to be able to compute the
 * tupledesc before actually creating the function.
 *
 * Returns NULL if there are not at least two OUT or INOUT arguments.
 */
TupleDesc
build_function_result_tupdesc_d(Datum proallargtypes,
								Datum proargmodes,
								Datum proargnames)
{
	TupleDesc	desc;
	ArrayType  *arr;
	int			numargs;
	Oid		   *argtypes;
	char	   *argmodes;
	Datum	   *argnames = NULL;
	Oid		   *outargtypes;
	char	  **outargnames;
	int			numoutargs;
	int			nargnames;
	int			i;

	/* Can't have output args if columns are null */
	if (proallargtypes == PointerGetDatum(NULL) ||
		proargmodes == PointerGetDatum(NULL))
		return NULL;

	/*
	 * We expect the arrays to be 1-D arrays of the right types; verify that.
	 * For the OID and char arrays, we don't need to use deconstruct_array()
	 * since the array data is just going to look like a C array of values.
	 */
	arr = DatumGetArrayTypeP(proallargtypes);	/* ensure not toasted */
	numargs = ARR_DIMS(arr)[0];
	if (ARR_NDIM(arr) != 1 ||
		numargs < 0 ||
		ARR_HASNULL(arr) ||
		ARR_ELEMTYPE(arr) != OIDOID)
		elog(ERROR, "proallargtypes is not a 1-D Oid array");
	argtypes = (Oid *) ARR_DATA_PTR(arr);
	arr = DatumGetArrayTypeP(proargmodes);		/* ensure not toasted */
	if (ARR_NDIM(arr) != 1 ||
		ARR_DIMS(arr)[0] != numargs ||
		ARR_HASNULL(arr) ||
		ARR_ELEMTYPE(arr) != CHAROID)
		elog(ERROR, "proargmodes is not a 1-D char array");
	argmodes = (char *) ARR_DATA_PTR(arr);
	if (proargnames != PointerGetDatum(NULL))
	{
		arr = DatumGetArrayTypeP(proargnames);	/* ensure not toasted */
		if (ARR_NDIM(arr) != 1 ||
			ARR_DIMS(arr)[0] != numargs ||
			ARR_HASNULL(arr) ||
			ARR_ELEMTYPE(arr) != TEXTOID)
			elog(ERROR, "proargnames is not a 1-D text array");
		deconstruct_array(arr, TEXTOID, -1, false, 'i',
						  &argnames, NULL, &nargnames);
		Assert(nargnames == numargs);
	}

	/* zero elements probably shouldn't happen, but handle it gracefully */
	if (numargs <= 0)
		return NULL;

	/* extract output-argument types and names */
	outargtypes = (Oid *) palloc(numargs * sizeof(Oid));
	outargnames = (char **) palloc(numargs * sizeof(char *));
	numoutargs = 0;
	for (i = 0; i < numargs; i++)
	{
		char	   *pname;

		if (argmodes[i] == PROARGMODE_IN ||
			argmodes[i] == PROARGMODE_VARIADIC)
			continue;
		Assert(argmodes[i] == PROARGMODE_OUT ||
			   argmodes[i] == PROARGMODE_INOUT ||
			   argmodes[i] == PROARGMODE_TABLE);
		outargtypes[numoutargs] = argtypes[i];
		if (argnames)
			pname = TextDatumGetCString(argnames[i]);
		else
			pname = NULL;
		if (pname == NULL || pname[0] == '\0')
		{
			/* Parameter is not named, so gin up a column name */
			pname = (char *) palloc(32);
			snprintf(pname, 32, "column%d", numoutargs + 1);
		}
		outargnames[numoutargs] = pname;
		numoutargs++;
	}

	/*
	 * If there is no output argument, or only one, the function does not
	 * return tuples.
	 */
	if (numoutargs < 2)
		return NULL;

	desc = CreateTemplateTupleDesc(numoutargs, false);
	for (i = 0; i < numoutargs; i++)
	{
		TupleDescInitEntry(desc, i + 1,
						   outargnames[i],
						   outargtypes[i],
						   -1,
						   0);
	}

	return desc;
}


/*
 * RelationNameGetTupleDesc
 *
 * Given a (possibly qualified) relation name, build a TupleDesc.
 *
 * Note: while this works as advertised, it's seldom the best way to
 * build a tupdesc for a function's result type.  It's kept around
 * only for backwards compatibility with existing user-written code.
 */
TupleDesc
RelationNameGetTupleDesc(const char *relname)
{
	RangeVar   *relvar;
	Relation	rel;
	TupleDesc	tupdesc;
	List	   *relname_list;

	/* Open relation and copy the tuple description */
	relname_list = stringToQualifiedNameList(relname);
	relvar = makeRangeVarFromNameList(relname_list);
	rel = relation_openrv(relvar, AccessShareLock);
	tupdesc = CreateTupleDescCopy(RelationGetDescr(rel));
	relation_close(rel, AccessShareLock);

	return tupdesc;
}

/*
 * TypeGetTupleDesc
 *
 * Given a type Oid, build a TupleDesc.  (In most cases you should be
 * using get_call_result_type or one of its siblings instead of this
 * routine, so that you can handle OUT parameters, RECORD result type,
 * and polymorphic results.)
 *
 * If the type is composite, *and* a colaliases List is provided, *and*
 * the List is of natts length, use the aliases instead of the relation
 * attnames.  (NB: this usage is deprecated since it may result in
 * creation of unnecessary transient record types.)
 *
 * If the type is a base type, a single item alias List is required.
 */
TupleDesc
TypeGetTupleDesc(Oid typeoid, List *colaliases)
{
	TypeFuncClass functypclass = get_type_func_class(typeoid);
	TupleDesc	tupdesc = NULL;

	/*
	 * Build a suitable tupledesc representing the output rows
	 */
	if (functypclass == TYPEFUNC_COMPOSITE)
	{
		/* Composite data type, e.g. a table's row type */
		tupdesc = lookup_rowtype_tupdesc_copy(typeoid, -1);

		if (colaliases != NIL)
		{
			int			natts = tupdesc->natts;
			int			varattno;

			/* does the list length match the number of attributes? */
			if (list_length(colaliases) != natts)
				ereport(ERROR,
						(errcode(ERRCODE_DATATYPE_MISMATCH),
						 errmsg("number of aliases does not match number of columns")));

			/* OK, use the aliases instead */
			for (varattno = 0; varattno < natts; varattno++)
			{
				char	   *label = strVal(list_nth(colaliases, varattno));

				if (label != NULL)
					namestrcpy(&(tupdesc->attrs[varattno]->attname), label);
			}

			/* The tuple type is now an anonymous record type */
			tupdesc->tdtypeid = RECORDOID;
			tupdesc->tdtypmod = -1;
		}
	}
	else if (functypclass == TYPEFUNC_SCALAR)
	{
		/* Base data type, i.e. scalar */
		char	   *attname;

		/* the alias list is required for base types */
		if (colaliases == NIL)
			ereport(ERROR,
					(errcode(ERRCODE_DATATYPE_MISMATCH),
					 errmsg("no column alias was provided")));

		/* the alias list length must be 1 */
		if (list_length(colaliases) != 1)
			ereport(ERROR,
					(errcode(ERRCODE_DATATYPE_MISMATCH),
			  errmsg("number of aliases does not match number of columns")));

		/* OK, get the column alias */
		attname = strVal(linitial(colaliases));

		tupdesc = CreateTemplateTupleDesc(1, false);
		TupleDescInitEntry(tupdesc,
						   (AttrNumber) 1,
						   attname,
						   typeoid,
						   -1,
						   0);
	}
	else if (functypclass == TYPEFUNC_RECORD)
	{
		/* XXX can't support this because typmod wasn't passed in ... */
		ereport(ERROR,
				(errcode(ERRCODE_DATATYPE_MISMATCH),
				 errmsg("could not determine row description for function returning record")));
	}
	else
	{
		/* crummy error message, but parser should have caught this */
		elog(ERROR, "function in FROM has unsupported return type");
	}

	return tupdesc;
}



