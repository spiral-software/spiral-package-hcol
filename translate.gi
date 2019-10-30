
# Copyright 2018-2019, Carnegie Mellon University
# See LICENSE for details

Class(implies,  AutoFoldExp, rec(    computeType := self >> TBool      ));

Class(RulesTest, RuleSet, rec(inType := "iCode", outType := "iCode"));
RewriteRules(RulesTest, rec(
 float_reduction  := ARule(DirectSum, [@(1), @(2, OLCompose, e->ObjId(e.child(1))=Reduction)],
                        e->[DirectSum(@(2).val, @(1).val)]),
    ));

Class(RulesEagarEval, RuleSet, rec(inType := "iCode", outType := "iCode"));
RewriteRules(RulesEagarEval, rec(
		eagar_eval_eq := Rule([@(1, eq), @(2), @(3).cond( e->e=@(2).val)],
                    e->let(V(true))),
					
		eagar_eval_ands_1 := Rule([@(1, logic_and), 
										@(2, Value).cond(e->IsBool(e.v)), 		
										@(3,Value).cond(e->IsBool(e.v))],
                    e->logic_and(@(2).val, @(3).val)),
		
		eagar_eval_ands_2 := Rule([@(1, logic_and), 
										@(2, Value).cond(e->IsBool(e.v)), 		
										@(3)],
                    e->Cond(@(2).val.v, @(3).val, V(false))),
		
		eagar_eval_ands_3 := Rule([@(1, logic_and), 
										@(2), 		
										@(3, Value).cond(e->IsBool(e.v))],
                    e->Cond(@(3).val.v, @(2).val, V(false))),
		
));


update_params := function(cx, d)
  cx.opts.params := cx.opts.params::[d];
end;
	
Class(RulesTranslate, RuleSet, rec(inType := "iCode", outType := "SigmaSPL"));
RewriteRules(RulesTranslate, rec(
        abs_inclusion := ARule(logic_and, [@(1,implies), @(2,implies, e->let(
                                 e.args[1].args[1]=@(1).val.args[1].args[1] and    #anthesdent must be the same 
                                 e.args[1].args[2]=@(1).val.args[1].args[2] and    #anthesdent must be the same 
                                 ((ObjId(e.args[1])=leq and ObjId(@(1).val.args[1])=geq) or    
                                  (ObjId(e.args[1])=geq and ObjId(@(1).val.args[1])=leq)) and 
                                 e.args[2].args[2]=@(1).val.args[2].args[2]))],
                    e->[let(x := var.fresh_t("x", T_Real(32)), 
                             i := Ind(1), 
                                PointWise(1, Lambda([x, i], ObjId(@(1).val.args[2])(abs(@(2).val.args[1].args[1]), @(1).val.args[2].args[2]))))]),

        ands_translate := ARule(logic_and, [@(1), @(2)], 
                   e-> [let(i := Ind(1), x := var.fresh_t("x", T_Real(32)), 
                           lhs := ObjId(@(1).val), rhs:= ObjId(@(2).val),
                          OLCompose(
                            Reduction(2, (a, b)->logic_and(a, b), V(true), False),
                            DirectSum(
                                Cond(lhs<>PointWise, PointWise(1, Lambda([x, i], @(1).val)), @(1).val), 
                                Cond(rhs<>PointWise, PointWise(1, Lambda([x, i], @(2).val)), @(2).val)  ))  )]),
        ors_translate := ARule(logic_or, [@(1), @(2)], 
                   e-> [let(i := Ind(1), x := var.fresh_t("x", T_Real(32)), 
                           lhs := ObjId(@(1).val), rhs:= ObjId(@(2).val),
                          OLCompose(
                          Reduction(2, (a, b)->logic_or(a, b), V(false), False),
                          DirectSum(
                                Cond(lhs<>PointWise, PointWise(1, Lambda([x, i], @(1).val)), @(1).val), 
                                Cond(rhs<>PointWise, PointWise(1, Lambda([x, i], @(2).val)), @(2).val)  ))  )]),
	
		
        undo_nesting := Rule(@(1,PointWise, e->IsLambda(e.op) and IsSPL(e.op.expr)),  
                    e->Cond(
						ObjId(e.op.expr).name="OLCompose", OLCompose(e.op.expr.children()),
						ObjId(e.op.expr).name="PointWise", PointWise(e.op.expr.N, Lambda( e.op.expr.op.vars, e.op.expr.op.expr)), 
Error("Not Implemented")						)),
							
		swap_ds_child := Rule([@(1, DirectSum), @(2).cond(e->ObjId(e)<>OLCompose), [@(3, OLCompose), @(4, Reduction), @(5)]],
			e->DirectSum(@(3).val, @(2).val)),
			
		swap_ds_child_1 := ARule(DirectSum, [@(1, PointWise), @(2, OLCompose)], 
			e->[DirectSum(@(2).val, @(1).val)]),
			
		max_intro := Rule([@(1, OLCompose), @(2, Reduction).cond(e->e.idval=false and e.N=2), 
						[@(3, DirectSum), @(4, PointWise), 
							@(5, PointWise).cond(e->ObjId(e.op.expr)=ObjId(@(4).val.op.expr) and
								ObjId(e.op.expr) = gt and
								e.op.expr.args[2] = @(4).val.op.expr.args[2])]],
			e-> PointWise(1, Lambda(@(4).val.op.vars, gt(max(@(4).val.op.expr.args[1], @(5).val.op.expr.args[1]), @(4).val.op.expr.args[2])))  ),

		
		reduce_reduction := Rule([@(1, OLCompose), @(2, Reduction), [@(3, DirectSum), [@(4, OLCompose), @(5, Reduction).cond(e->e.idval=@(2).val.idval), @(6)], @(7)]],
			e-> OLCompose(
					Reduction(@(2).val.N + @(5).val.N-1, @(2).val.op, @(2).val.idval, @(2).val.isSaturated), 
					DirectSum(@(6).val, @(7).val) )),

		
		intro_polynomial := Rule([@(1, PointWise), @(2), @(3, Lambda).cond(e->ObjId(e.expr)=gt and 
																			  ObjId(e.expr.args[1]) = max and                                   #check max of all abs values
																			  Length(Filtered(List(e.expr.args[1].args, i->ObjId(i)=abs), x->x=false))=0 and           
																			  Length(Collect(e.expr.args[2], pow))<>0                           #has degree higher than 1
																			  #Length(Filtered(List(Collect(e.expr.args[2], pow), i->IsInt(i.args[2])), x->x=false))=0  # and exponents are numeric																			  
															  				   #still need to check for sub within the abs operator to be sure that it is TDistance

																			  )],																				
			(e, cx)->let(d := var.fresh_t("d", TPtr(T_Real(64))), 
				   update_params(cx,d),
				   degree := ApplyFunc(max, List(Collect(@(3).val.expr.args[2], pow), i->i.args[2])),				   
				   TLess(TEvalPolynomial(degree.v, d), TDistance(TInfinityNorm(2)))))
    ));
	

	
TInt_Base.check := v->Cond(IsExp(v), Int(v.ev()),
						   IsInt(v), v, 
						   IsBool(v), When(v, true, false),
						    IsDouble(v) and IsInt(IntDouble(v)), IntDouble(v),
							IsValue(v) and IsInt(v.v), v.v,
							Error("<v> must be an integer or an expression"));

TReal.check := (self, v) >> Cond(
							IsExp(v), 		ReComplex(Complex(code.EvalScalar(v))),
							IsInt(v), 		Double(v),
							IsRat(v), 		v, 
							IsDouble(v), When(AbsFloat(v) < self.cutoff, 0.0, v),
							IsCyc(v), ReComplex(Complex(v)),
							IsComplex(v),	ReComplex(v), 							
							IsBool(v), 		When(v, true, false),
							Error("<v> must be a double or an expression"));

