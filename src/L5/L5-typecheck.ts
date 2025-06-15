// L5-typecheck
// ========================================================
import { equals, map, zipWith } from 'ramda';
import { isAppExp, isBoolExp, isDefineExp, isIfExp, isLetrecExp, isLetExp, isLitExp, isNumExp,
         isPrimOp, isProcExp, isProgram, isSetExp, isStrExp, isVarRef, parseL5Exp, unparse,
         AppExp, BoolExp, DefineExp, Exp, IfExp, LetrecExp, LetExp, LitExp, NumExp,
         Parsed, PrimOp, ProcExp, Program, SetExp, StrExp, parseL5Program } from "./L5-ast";
import { applyTEnv, makeEmptyTEnv, makeExtendTEnv, TEnv } from "./TEnv";
import { isPairTExp, isProcTExp, makeBoolTExp, makeNumTExp, makePairTExp, makeProcTExp, makeStrTExp, makeVoidTExp,
         parseTE, unparseTExp,
         BoolTExp, NumTExp, PairTExp, StrTExp, TExp, VoidTExp } from "./TExp";
import { isEmpty, allT, first, rest, NonEmptyList, List, isNonEmptyList } from '../shared/list';
import { Result, makeFailure, bind, makeOk, zipWithResult } from '../shared/result';
import { parse as p } from "../shared/parser";
import { format } from '../shared/format';

// Purpose: Check that type expressions are equivalent
// as part of a fully-annotated type check process of exp.
// Return an error if the types are different - true otherwise.
// Exp is only passed for documentation purposes.
const checkEqualType = (te1: TExp, te2: TExp, exp: Exp): Result<true> =>
  equals(te1, te2) ? makeOk(true) :
  bind(unparseTExp(te1), (te1: string) =>
    bind(unparseTExp(te2), (te2: string) =>
        bind(unparse(exp), (exp: string) => 
            makeFailure<true>(`Incompatible types: ${te1} and ${te2} in ${exp}`))));

// Compute the type of L5 AST exps to TE
// ===============================================
// Compute a Typed-L5 AST exp to a Texp on the basis
// of its structure and the annotations it contains.

// Purpose: Compute the type of a concrete fully-typed expression
export const L5typeof = (concreteExp: string): Result<string> =>
    bind(p(concreteExp), (x) =>
        bind(parseL5Exp(x), (e: Exp) => 
            bind(typeofExp(e, makeEmptyTEnv()), unparseTExp)));

// Purpose: Compute the type of an expression
// Traverse the AST and check the type according to the exp type.
// We assume that all variables and procedures have been explicitly typed in the program.
export const typeofExp = (exp: Parsed, tenv: TEnv): Result<TExp> =>
    isNumExp(exp) ? makeOk(typeofNum(exp)) :
    isBoolExp(exp) ? makeOk(typeofBool(exp)) :
    isStrExp(exp) ? makeOk(typeofStr(exp)) :
    isPrimOp(exp) ? typeofPrim(exp) :
    isVarRef(exp) ? applyTEnv(tenv, exp.var) :
    isIfExp(exp) ? typeofIf(exp, tenv) :
    isProcExp(exp) ? typeofProc(exp, tenv) :
    isAppExp(exp) ? typeofApp(exp, tenv) :
    isLetExp(exp) ? typeofLet(exp, tenv) :
    isLetrecExp(exp) ? typeofLetrec(exp, tenv) :
    isDefineExp(exp) ? typeofDefine(exp, tenv) :
    isProgram(exp) ? typeofProgram(exp, tenv) :
    isSetExp(exp) ? typeofSet(exp, tenv) :
    isLitExp(exp) ? typeofLit(exp, tenv) :
    makeFailure(`Unknown type: ${format(exp)}`);

// Purpose: Compute the type of a sequence of expressions
// Check all the exps in a sequence - return type of last.
// Pre-conditions: exps is not empty.
export const typeofExps = (exps: List<Exp>, tenv: TEnv): Result<TExp> =>
    isNonEmptyList<Exp>(exps) ? 
        isEmpty(rest(exps)) ? typeofExp(first(exps), tenv) :
        bind(typeofExp(first(exps), tenv), _ => typeofExps(rest(exps), tenv)) :
    makeFailure(`Unexpected empty list of expressions`);


// a number literal has type num-te
export const typeofNum = (n: NumExp): NumTExp => makeNumTExp();

// a boolean literal has type bool-te
export const typeofBool = (b: BoolExp): BoolTExp => makeBoolTExp();

// a string literal has type str-te
const typeofStr = (s: StrExp): StrTExp => makeStrTExp();

// primitive ops have known proc-te types
const numOpTExp = parseTE('(number * number -> number)');
const numCompTExp = parseTE('(number * number -> boolean)');
const boolOpTExp = parseTE('(boolean * boolean -> boolean)');

// Pair operations and other primitives with proper type signatures
export const typeofPrim = (p: PrimOp): Result<TExp> =>
    (p.op === '+') ? numOpTExp :
    (p.op === '-') ? numOpTExp :
    (p.op === '*') ? numOpTExp :
    (p.op === '/') ? numOpTExp :
    (p.op === 'and') ? boolOpTExp :
    (p.op === 'or') ? boolOpTExp :
    (p.op === '>') ? numCompTExp :
    (p.op === '<') ? numCompTExp :
    (p.op === '=') ? numCompTExp :
    // Pair operations with proper Pair type syntax
    (p.op === 'cons') ? parseTE('(T1 * T2 -> (Pair T1 T2))') :
    (p.op === 'car') ? parseTE('((Pair T1 T2) -> T1)') :
    (p.op === 'cdr') ? parseTE('((Pair T1 T2) -> T2)') :
    (p.op === 'list') ? parseTE('(T* -> (List T))') :
    // Type predicates - use different signature for each op with a TVar to avoid capture
    (p.op === 'number?') ? parseTE('(T -> boolean)') :
    (p.op === 'boolean?') ? parseTE('(T -> boolean)') :
    (p.op === 'string?') ? parseTE('(T -> boolean)') :
    (p.op === 'list?') ? parseTE('(T -> boolean)') :
    (p.op === 'pair?') ? parseTE('(T -> boolean)') :
    (p.op === 'symbol?') ? parseTE('(T -> boolean)') :
    (p.op === 'not') ? parseTE('(boolean -> boolean)') :
    (p.op === 'eq?') ? parseTE('(T1 * T2 -> boolean)') :
    (p.op === 'string=?') ? parseTE('(T1 * T2 -> boolean)') :
    (p.op === 'display') ? parseTE('(T -> void)') :
    (p.op === 'newline') ? parseTE('(Empty -> void)') :
    makeFailure(`Primitive not yet implemented: ${p.op}`);

// Purpose: compute the type of an if-exp
// Typing rule:
//   if type<test>(tenv) = boolean
//      type<then>(tenv) = t1
//      type<else>(tenv) = t1
// then type<(if test then else)>(tenv) = t1
export const typeofIf = (ifExp: IfExp, tenv: TEnv): Result<TExp> => {
    const testTE = typeofExp(ifExp.test, tenv);
    const thenTE = typeofExp(ifExp.then, tenv);
    const altTE = typeofExp(ifExp.alt, tenv);
    const constraint1 = bind(testTE, testTE => checkEqualType(testTE, makeBoolTExp(), ifExp));
    const constraint2 = bind(thenTE, (thenTE: TExp) =>
                            bind(altTE, (altTE: TExp) =>
                                checkEqualType(thenTE, altTE, ifExp)));
    return bind(constraint1, (_c1: true) =>
                bind(constraint2, (_c2: true) =>
                    thenTE));
};

// Purpose: compute the type of a proc-exp
// Typing rule:
// If   type<body>(extend-tenv(x1=t1,...,xn=tn; tenv)) = t
// then type<lambda (x1:t1,...,xn:tn) : t exp)>(tenv) = (t1 * ... * tn -> t)
export const typeofProc = (proc: ProcExp, tenv: TEnv): Result<TExp> => {
    const argsTEs = map((vd) => vd.texp, proc.args);
    const extTEnv = makeExtendTEnv(map((vd) => vd.var, proc.args), argsTEs, tenv);
    const constraint1 = bind(typeofExps(proc.body, extTEnv), (body: TExp) => 
                            checkEqualType(body, proc.returnTE, proc));
    return bind(constraint1, _ => makeOk(makeProcTExp(argsTEs, proc.returnTE)));
};

// Purpose: compute the type of an app-exp
// Typing rule:
// If   type<rator>(tenv) = (t1*..*tn -> t)
//      type<rand1>(tenv) = t1
//      ...
//      type<randn>(tenv) = tn
// then type<(rator rand1...randn)>(tenv) = t
// We also check the correct number of arguments is passed.
export const typeofApp = (app: AppExp, tenv: TEnv): Result<TExp> =>
    bind(typeofExp(app.rator, tenv), (ratorTE: TExp) => {
        if (! isProcTExp(ratorTE)) {
            return bind(unparseTExp(ratorTE), (rator: string) =>
                        bind(unparse(app), (exp: string) =>
                            makeFailure<TExp>(`Application of non-procedure: ${rator} in ${exp}`)));
        }
        if (app.rands.length !== ratorTE.paramTEs.length) {
            return bind(unparse(app), (exp: string) => makeFailure<TExp>(`Wrong parameter numbers passed to proc: ${exp}`));
        }
        const constraints = zipWithResult((rand, trand) => bind(typeofExp(rand, tenv), (typeOfRand: TExp) => 
                                                                checkEqualType(typeOfRand, trand, app)),
                                          app.rands, ratorTE.paramTEs);
        return bind(constraints, _ => makeOk(ratorTE.returnTE));
    });

// Purpose: compute the type of a let-exp
// Typing rule:
// If   type<val1>(tenv) = t1
//      ...
//      type<valn>(tenv) = tn
//      type<body>(extend-tenv(var1=t1,..,varn=tn; tenv)) = t
// then type<let ((var1 val1) .. (varn valn)) body>(tenv) = t
export const typeofLet = (exp: LetExp, tenv: TEnv): Result<TExp> => {
    const vars = map((b) => b.var.var, exp.bindings);
    const vals = map((b) => b.val, exp.bindings);
    const varTEs = map((b) => b.var.texp, exp.bindings);
    const constraints = zipWithResult((varTE, val) => bind(typeofExp(val, tenv), (typeOfVal: TExp) => 
                                                            checkEqualType(varTE, typeOfVal, exp)),
                                      varTEs, vals);
    return bind(constraints, _ => typeofExps(exp.body, makeExtendTEnv(vars, varTEs, tenv)));
};

// Purpose: compute the type of a letrec-exp
// We make the same assumption as in L4 that letrec only binds proc values.
// Typing rule:
//   (letrec((p1 (lambda (x11 ... x1n1) body1)) ...) body)
//   tenv-body = extend-tenv(p1=(t11*..*t1n1->t1)....; tenv)
//   tenvi = extend-tenv(xi1=ti1,..,xini=tini; tenv-body)
// If   type<body1>(tenv1) = t1
//      ...
//      type<bodyn>(tenvn) = tn
//      type<body>(tenv-body) = t
// then type<(letrec((p1 (lambda (x11 ... x1n1) body1)) ...) body)>(tenv-body) = t
export const typeofLetrec = (exp: LetrecExp, tenv: TEnv): Result<TExp> => {
    const ps = map((b) => b.var.var, exp.bindings);
    const procs = map((b) => b.val, exp.bindings);
    if (! allT(isProcExp, procs))
        return makeFailure(`letrec - only support binding of procedures - ${format(exp)}`);
    const paramss = map((p) => p.args, procs);
    const bodies = map((p) => p.body, procs);
    const tijs = map((params) => map((p) => p.texp, params), paramss);
    const tis = map((proc) => proc.returnTE, procs);
    const tenvBody = makeExtendTEnv(ps, zipWith((tij, ti) => makeProcTExp(tij, ti), tijs, tis), tenv);
    const tenvIs = zipWith((params, tij) => makeExtendTEnv(map((p) => p.var, params), tij, tenvBody),
                           paramss, tijs);
    const types = zipWithResult((bodyI, tenvI) => typeofExps(bodyI, tenvI), bodies, tenvIs)
    const constraints = bind(types, (types: TExp[]) => 
                            zipWithResult((typeI, ti) => checkEqualType(typeI, ti, exp), types, tis));
    return bind(constraints, _ => typeofExps(exp.body, tenvBody));
};

// Purpose: compute the type of a define expression
// Typing rule:
//   (define (var : texp) val)
// If   type<val>(tenv) = texp
// then type<(define (var : texp) val)>(tenv) = void
export const typeofDefine = (exp: DefineExp, tenv: TEnv): Result<VoidTExp> => {
    const valTE = typeofExp(exp.val, tenv);
    const varTE = exp.var.texp;
    const constraint = bind(valTE, (valTE: TExp) => checkEqualType(varTE, valTE, exp));
    return bind(constraint, _ => makeOk(makeVoidTExp()));
};

// Purpose: compute the type of a set expression
// Typing rule:
//   (set! var val)
// If   type<val>(tenv) = t
//      type<var>(tenv) = t
// then type<(set! var val)>(tenv) = void
export const typeofSet = (exp: SetExp, tenv: TEnv): Result<TExp> => {
    const varTE = applyTEnv(tenv, exp.var.var);
    const valTE = typeofExp(exp.val, tenv);
    const constraint = bind(varTE, (varTE: TExp) =>
                           bind(valTE, (valTE: TExp) =>
                               checkEqualType(varTE, valTE, exp)));
    return bind(constraint, _ => makeOk(makeVoidTExp()));
};

// Purpose: compute the type of a literal expression
// Typing rule:
//   (quote <sexp>)
// The type depends on the structure of the s-expression
export const typeofLit = (exp: LitExp, tenv: TEnv): Result<TExp> => {
    const val = exp.val;
    
    // Basic atomic types
    if (typeof val === 'number') {
        return makeOk(makeNumTExp());
    } else if (typeof val === 'boolean') {
        return makeOk(makeBoolTExp());
    } else if (typeof val === 'string') {
        return makeOk(makeStrTExp());
    }
    
    // Handle compound values (pairs, lists)
    if (Array.isArray(val)) {
        // For pairs represented as arrays of length 2
        if (val.length === 2) {
            // Recursively determine types of pair elements
            const leftType = typeof val[0] === 'number' ? makeNumTExp() :
                           typeof val[0] === 'boolean' ? makeBoolTExp() :
                           typeof val[0] === 'string' ? makeStrTExp() :
                           undefined;
            const rightType = typeof val[1] === 'number' ? makeNumTExp() :
                            typeof val[1] === 'boolean' ? makeBoolTExp() :
                            typeof val[1] === 'string' ? makeStrTExp() :
                            undefined;
            
            if (leftType && rightType) {
                return makeOk(makePairTExp(leftType, rightType));
            }
        }
        // For other lists, return failure for now
        return makeFailure(`Complex list literal types not yet implemented: ${val}`);
    }
    
    // For symbols and other complex types
    return makeFailure(`Literal type not yet implemented: ${val}`);
};

// Purpose: compute the type of a program
// Typing rule:
//   (L5 <exp>+)
// If   type<exp1>(tenv) = t1
//      type<exp2>(extend-tenv-if-define(exp1, tenv)) = t2
//      ...
//      type<expn>(extend-tenv-if-define(exp1...expn-1, tenv)) = tn
// then type<(L5 <exp>+)>(tenv) = tn (type of last expression)
// 
// For each define expression, we extend the environment with the new variable binding
// For non-define expressions, we continue with the same environment
export const typeofProgram = (exp: Program, tenv: TEnv): Result<TExp> => {
    const exps = exp.exps;
    if (exps.length === 0) {
        return makeFailure("Empty program");
    }
    
    // Helper function to process expressions sequentially, threading environment for define expressions
    const processExpressions = (expressions: Exp[], currentTEnv: TEnv): Result<TExp> => {
        if (expressions.length === 0) {
            return makeFailure("Empty expressions list");
        }
        
        const [firstExp, ...restExps] = expressions;
        
        if (isDefineExp(firstExp)) {
            // For define expressions:
            // 1. Type check the define expression itself (should return void)
            // 2. Extend the environment with the new variable binding
            // 3. Continue with the rest of the expressions using the extended environment
            const defineTypeResult = typeofDefine(firstExp, currentTEnv);
            return bind(defineTypeResult, _ => {
                const extendedTEnv = makeExtendTEnv([firstExp.var.var], [firstExp.var.texp], currentTEnv);
                if (restExps.length === 0) {
                    // If this is the last expression and it's a define, return void
                    return makeOk(makeVoidTExp());
                } else {
                    // Continue with remaining expressions using extended environment
                    return processExpressions(restExps, extendedTEnv);
                }
            });
        } else {
            // For non-define expressions:
            // 1. Type check the expression
            // 2. If this is the last expression, return its type
            // 3. Otherwise, continue with the rest using the same environment
            const expTypeResult = typeofExp(firstExp, currentTEnv);
            return bind(expTypeResult, (expType: TExp) => {
                if (restExps.length === 0) {
                    // If this is the last expression, return its type
                    return makeOk(expType);
                } else {
                    // Continue with remaining expressions using the same environment
                    return processExpressions(restExps, currentTEnv);
                }
            });
        }
    };
    
    return processExpressions(exps, tenv);
};

export const L5programTypeof = (concreteExp: string): Result<string> =>
    bind(p(concreteExp), (x) =>
        bind(parseL5Program(x), (program: Program) => 
            bind(typeofProgram(program, makeEmptyTEnv()), unparseTExp)));
