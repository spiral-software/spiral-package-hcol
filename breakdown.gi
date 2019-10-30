
# Copyright 2018-2019, Carnegie Mellon University
# See LICENSE for details

#sin(a+b) = sin(a)cos(b) + cos(a)sin(b)
#cos(a+b) = cos(a)cos(b) - sin(a)sin(b)

# cos(a)x + sin(a)y 
# cos(a+b)x + sin(a+b)y
# cos(a)cos(b)x - sin(a)sin(b)x + sin(a)cos(b)y + cos(a)sin(b)y
# cos(a)cos(b)x + sin(a)cos(b)y + cos(a)sin(b)y - sin(a)sin(b)x
# cos(b)[cos(a)x+sin(a)y] + sin(b)[cos(a)y-sin(a)x]


NewRulesFor(HF, rec(
  HF_dummy := rec(
    applicable := (self, nt) >> true,
    forTransposition := false, 
    apply := (t, c, nt) ->
     let( 
         size := When(IsArrayT(t.params[1].t), t.params[1].t.size, Rows(t.params[1])),
       GathH(8, size, t.params[2]*size, 1)
    )
  )
));

NewRulesFor(TForAllInd, rec(
  TForAllInd_loop := rec(  
    forTransposition := false,
    applicable := (self, nt) >> true,
    children := nt -> [ [ nt.params[2].withTags(nt.getTags()) ] ],
    apply := (t, c, nt) ->
      let(i := t.params[1], 
          IterVStack(i, i.range,
	    OLCompose(
	      c[1],
	      GathH(Cols(c[1]), Cols(c[1]), Cols(c[1])*i, 1)
	     )
	  )
      )
  )
));


NewRulesFor(TComputeDist, rec(
  TComputeDistBase := rec(
    apply := (t, c, nt) ->
      let(x := var.fresh_t("r", TReal), y:= var.fresh_t("r", TReal),
      OLCompose(
        Reduction(t.params[1], (a,b)->min(a,b), V(1000.0), False),
	BinOp(t.params[1], Lambda([x, y], add(x, y)))
      )
  ))
));


NewRulesFor(TForAnyInd, rec(
    TForAnyInd_loop := rec(
        forTransposition := false,
        applicable := (self, nt) >> true,
        children := nt -> [ [ nt.params[2].withTags(nt.getTags()) ] ],
        apply := (t, c, nt) -> 
	   let(iter := t.params[1], 
	     OLCompose(
	       Reduction(iter.range, (a,b)->logic_or(a,b), V(false), 
	       a->eq(a, V(true))), IterVStack(iter, c[1]))),
    )
));


NewRulesFor(TInsidePoly, rec(
    TInsidePoly_EvalLinSys := rec(
        applicable := (self, nt) >> ObjId(nt.params[1]) = LinearSystem,
        forTransposition := false,
        children := nt -> [ [ TEvalLinSys(nt.params[1]).withTags(nt.getTags()) ] ],
        apply := (t, C, Nonterms) -> let(
            evalsys := C[1], 
            i := Ind(Rows(evalsys)), x := var.fresh_t("r", TDouble), 
            cmp0 := PointWise(Rows(evalsys), Lambda([x,i], leq(x, V(0)))),
            forall_op := Reduction(Rows(evalsys), (a,b)->logic_and(a,b), V(true), a->eq(a, V(false))),
            OLCompose(forall_op, cmp0, evalsys))
    )
));

NewRulesFor(TEvalLinSys, rec(
    TEvalLinSys_TMatVecProd := rec(
        applicable := (self, nt) >> ObjId(nt.params[1]) = LinearSystem,
        children := nt -> [ [ TMatVecProd(nt.params[1].mat).withTags(nt.getTags()) ] ],
        forTransposition := false,
        apply := (t, C, Nonterms) -> let(linsys := t.params[1], A := linsys.mat, b := linsys.rhs, n :=linsys.dims()[1],
            x := var.fresh_t("r", TDouble), i := Ind(n),
            OLCompose(PointWise(n, Lambda([x,i], sub(x, nth(b, i)))), C[1]))
    )
));

NewRulesFor(TMatVecProd, rec(
    TMatVecProd_Term := rec(
        applicable := (self, nt) >> true,
        forTransposition := false,
        apply := (t, C, Nonterms) -> let(mat := t.params[1], n := mat.dims()[1], m := mat.dims()[2], i := Ind(n),   
            IterVStack(i, n, ScalarProd(m, nth(mat, i))))
    )
));

NewRulesFor(TInfinityNorm, rec(
    TInfinityNorm_Base := rec(
        applicable := True,
        forTransposition := false,
        apply := (t, C, Nonterms) -> let(n :=t.dims()[2], 
            x := var.fresh_t("r", TDouble), i := Ind(n),
            OLCompose(Reduction(n, (a,b)->max(a,b), V(0.0), False), PointWise(n, Lambda([x,i], abs(x)))))
    )
));

NewRulesFor(TDistance, rec(
    TDistance_Base := rec(
        applicable := True,
        forTransposition := false,
        children := nt -> [[nt.params[1]]],
        apply := (t, C, Nonterms) -> let(n :=C[1].dims()[2], x := var.fresh_t("r", TDouble), y := var.fresh_t("r", TDouble),
            OLCompose(C[1], BinOp(n, Lambda([x,y], sub(x,y)))))
    )
));

NewRulesFor(TEvalPolynomial, rec(
    TEvalPolynomial_Base := rec(
        applicable := True,
        forTransposition := false,
        apply := (t, C, Nonterms) -> let(n := t.params[1]+1, x := var.fresh_t("r", TDouble), y := var.fresh_t("r", TDouble),
            OLCompose(ScalarProd(n, t.params[2]), Induction(n, Lambda([x,y], mul(x, y)), V(1.0))))
    )
));

NewRulesFor(TLess, rec(
    TLess_Base := rec(
        applicable := True,
        forTransposition := false,
        children := nt -> [nt.params],
        apply := (t, c, Nonterms) -> let(
			n :=t.dims()[1], 
			x := var.fresh_t("r", TDouble), 
			y := var.fresh_t("r", TDouble),
			OLCompose(
				BinOp(n, Lambda([x,y], lt(x,y))), DirectSum(c[1], c[2]) )
    )
)));


NewRulesFor(TGreater, rec(
    TGreater_Base := rec(
        applicable := True,
        forTransposition := false,
        children := nt -> [nt.params],
        apply := (t, c, Nonterms) -> let(
      n :=t.dims()[1], 
      x := var.fresh_t("r", TDouble), 
      y := var.fresh_t("r", TDouble),
      OLCompose(
        BinOp(n, Lambda([x,y], gt(x,y))), DirectSum(c[1], c[2]) )
    )
)));

NewRulesFor(TLessEqual, rec(
    TLessEqual_Base := rec(
        applicable := True,
        forTransposition := false,
        children := nt -> [nt.params],
        apply := (t, c, Nonterms) -> let(
      n :=t.dims()[1], 
      x := var.fresh_t("r", TDouble), 
      y := var.fresh_t("r", TDouble),
      OLCompose(
        BinOp(n, Lambda([x,y], leq(x,y))), DirectSum(c[1], c[2]) )
    )
)));

NewRulesFor(TGreaterEqual, rec(
    TGreaterEqual_Base := rec(
        applicable := True,
        forTransposition := false,
        children := nt -> [nt.params],
        apply := (t, c, Nonterms) -> let(
      n :=t.dims()[1], 
      x := var.fresh_t("r", TDouble), 
      y := var.fresh_t("r", TDouble),
      OLCompose(
        BinOp(n, Lambda([x,y], geq(x,y))), DirectSum(c[1], c[2]) )
    )
)));

NewRulesFor(TEqual, rec(
    TEqual_Base := rec(
        applicable := True,
        forTransposition := false,
        children := nt -> [nt.params],
        apply := (t, c, Nonterms) -> let(
      n :=t.dims()[1], 
      x := var.fresh_t("r", TDouble), 
      y := var.fresh_t("r", TDouble),
      OLCompose(
        BinOp(n, Lambda([x,y], eq(x,y))), DirectSum(c[1], c[2]) )
    )
)));


NewRulesFor(TCond, rec(
	Cond_Base := rec(
		applicable := True,
		forTransposition := false,
		children := nt -> [nt.params],
		apply := (t, c, Nonterms) -> let(
			COND(c[1], c[2], c[3])
		)
	)
));


NewRulesFor(TConstant, rec(
    TConstant_Base := rec(
       applicable := True, 
       forTransposition := false, 
       children := nt -> [nt.params], 
       apply := (t, C, Nonterms) -> let(x := var.fresh_t("r", TDouble), i := Ind(1), PointWise(1, Lambda([x, i], x)))
    )
));
