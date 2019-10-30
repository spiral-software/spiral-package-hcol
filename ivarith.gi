
# Copyright 2018-2019, Carnegie Mellon University
# See LICENSE for details

Class(cos, AutoFoldExp, rec(
  computeType := (self) >> TReal,
  
));

Class(sin, AutoFoldExp, rec(
  computeType := (self) >> TReal,
));

Class(tan, AutoFoldExp, rec(
  computeType := (self) >> TReal,
));



Class(TIVReal, AtomicTyp, rec(
    hash := (_val, size) -> let(val := When(IsList(_val), _val, [_val, _val]),
        h := DoubleRep64(val[1]) + DoubleRep64(val[2]),
        1 + (h mod size)),
    check := v -> Cond(IsDouble(v) or IsList(v) and Length(v) = 2 and v[1] <= v[2], v, Error("<v> must be a Double or an ordered list of length 2")),
    realType    := self >> self,
    print := self >> Print(self.__name__, "(", self.t, ")"),
    base_t := self >> self.t,
    zero := self >> self.value(0.0),
    one := self >> self.value(1.0),
    __call__ := (self, t) >>
        WithBases(self, rec(
        t    := Checked(IsType(t), t),
        operations := TypOps))
));

Class(TIVBool, AtomicTyp, rec(
    hash := (val, size) -> 1 + (InternalHash(val) mod size),
    check := v -> Cond(IsInt(v) and v in [0, 1, -1], v, Error("<v> must be in [-1, 0, 1]")),
    zero := self >> self.value(0),
    one := self >> self.value(1)
));

Class(ivenv, chain);


Class(RulesHCOLIVArithType, RuleSet, rec(inType := "iCode", outType := "iCode"));
RewriteRules(RulesHCOLIVArithType, rec(  
	ivenv_prop_types_bools := ARule(ivenv, [[@(1, assign), @(2,var).cond(e->e.t<>TInt), 
		@(3).cond(e-> e.t<>@(2).val.t and e.t=TBool)], @(4)], 
        e->let( 						
		nvar := var.fresh_t("n", TInt), 
		#Print("New Type 2: ", @(1).val,"(",@(2).val, ",",@(3).val,")\n", @(2).val.t, " <> ", @(3).val.t, "\n New Var Type: ", nvar, ",",nvar.t," \n"),
	  [decl([nvar], SubstVars(chain(assign(nvar, @(3).val), @(4).val), rec((@(2).val.id) := nvar )))] ) ),

    ivenv_prop_types := ARule(ivenv, [[@(1, assign), @(2,var), 
		@(3).cond(e-> e.t<>@(2).val.t and not (e.t in [TVect(T_Real(64), 2), TIVReal, TBool]))], @(4,...)], 
        e->let( 						
		nvar := var.fresh_t("n", @(3).val.t), 
		#Print("New Type: ", @(1).val,"(",@(2).val, ",",@(3).val,")", @(2).val.t, " <> ", @(3).val.t, " ", nvar, "\n", @(4).val, "\n"),
	  [decl([nvar], SubstVars(chain(assign(nvar, @(3).val), @(4).val), rec((@(2).val.id) := nvar )))] ) ),

));

Class(RulesHCOLIVArith, RuleSet, rec(inType := "iCode", outType := "iCode"));
RewriteRules(RulesHCOLIVArith, rec(
    ivenv_chain := Rule(@(1, ivenv, e->ForAny(e.cmds, f->ObjId(f) = chain)),
        e->ApplyFunc(ivenv, Flat(List(@(1).val.cmds, j->When(ObjId(j)=chain, j.cmds, j))))),
    ivenv_xyz_decl := ARule(ivenv, [@(1), @(2, decl)], 
        e->[decl(@(2).val.vars, chain(@(1).val, @(2).val.cmd))]),	
    ivenv_decl := Rule(@(1, ivenv, e->ObjId(e.cmds[1])=decl), 
        e -> decl(@(1).val.cmds[1].vars, ivenv(Concat([@(1).val.cmds[1].cmd], Drop(@(1).val.cmds, 1))))),
    ivenv_drop_selfassign := ARule(ivenv, [@(1, assign, e->IsVar(e.loc) and IsVar(e.exp) and e.exp=e.loc), @(2)], 
        e->[@(2).val]), 
    ivenv_creturn := Rule(@(1, ivenv, e->ObjId(Last(e.cmds))=creturn),
        e->chain(ivenv(DropLast(@(1).val.cmds, 1)), Last(@(1).val.cmds))),
    loop_pull_const_array_tcast := Rule([@(1, loop), @(2),  @(3), [@(4, chain), [@(5, assign), @(6,var), [@(7, tcast), @(8), @(9,nth, e->IsValue(e.idx))]],...]], 
        e->let(#Print(e, "\n"), 
		chain(@(5).val, loop(@(1).val.var, @(1).val.range, chain(Drop(@(4).val.cmds,1)))))),
    ivenv_state := Rule([@(1, tcast), @(2), @@(3, nth, (e, cx)->IsBound(cx.opts.state) and e.loc.id=cx.opts.state.id)], 
        (e, cx)->nth(cx.opts.ivstate, e.args[2].idx) )
));



RulesCodeUnrollHACMIVArth := CopyFields(MergedRuleSet( RulesHCOLIVArith, RulesUnrollHCOL, RulesStrengthReduce,  RulesCodeHCOL), 
    rec(inType:="iCode", outType := "iCode"));

RulesCodeHACMIVArth := CopyFields(MergedRuleSet(RulesStrengthReduce, RulesCodeHCOL, RulesHCOLIVArith), 
    rec(inType:="iCode", outType := "iCode"));

RulesCodeUnrollHACMIVArthType := CopyFields(MergedRuleSet(RulesCodeUnrollHACMIVArth, RulesHCOLIVArithType), 
	rec(inType :="iCode", outType:="iCode"));
	
Class(IVArithMixin, rec(
    precision := "double", 
    TRealCtype := "double",
    IVRealType := TIVReal(T_Real(64)),
    IVBoolType := TInt,
    IVValueType := TIVReal(T_Real(64)),
    codeRuleSet := RulesCodeUnrollHACMIVArth
));

Class(ivExp, errExp);

Class(RealEPS, errExp);

Class(RealMPS, errExp);


Class(IVArith, SumsBase, BaseContainer, rec(
    rng := meth(self) return self._children[1].rng(); end,
    dmn := meth(self) return self._children[1].dmn(); end,
    toOperator := self >> (vec -> self.child(1).toOperator()(vec))
));

Class(TIVArith, Tagged_tSPL_Container, rec(
    abbrevs :=  [ s -> Checked(IsSPL(s), [s]) ],
    transpose := self >> CopyFields(self, rec(transposed := not self.transposed)),
    dims := self >> [self.params[1].dims()[1], self.params[1].dims()[2]],
    isReal := True,
    toOperator := self >> (vec -> let(r := self.params[1].toOperator()(vec), List(r, i->ivExp(i))))
));

NewRulesFor(TIVArith, rec(
    TIVArith_Base := rec(
        applicable := True,
        forTransposition := false,
        children := nt -> [[nt.params[1]]],
        apply := (t, C, Nonterms) -> IVArith(C[1])
    ) 
));

HCOLSumsGen.IVArith := (self, o, opts) >> IVArith(self(o.child(1), opts));

Class(TypeUpdate, HierarchicalVisitor, rec(
	__call__ := meth(arg)
        local res;
        res := ApplyFunc(arg[1].visit, arg{[2..Length(arg)]});
        return res;
    end,
	func := (self, o, opts) >> let(func(o.ret, o.id, o.params, self(o.cmd, opts))),    
	decl := (self, o, opts) >>  decl(o.vars, self(o.cmd, opts)),
	chain := (self, o, opts) >> chain(List(o.cmds, i-> self(i, opts))),
    ivenv := (self, o, opts) >> ivenv(List(o.cmds, i-> self(i, opts))),
    loop := (self, o, opts) >>  loop(o.var, o.range, self(o.cmd, opts)),
	
	assign := (self, o, opts) >> assign(o.loc, self(o.exp, opts)),
	add := (self, o, opts) >> add(self(o.args[1], opts), self(o.args[2], opts)),	
	sub := (self, o, opts) >> sub(self(o.args[1], opts), self(o.args[2], opts)),
	mul := (self, o, opts) >> mul(self(o.args[1], opts), self(o.args[2], opts)),
	div := (self, o, opts) >> div(self(o.args[1], opts), self(o.args[2], opts)),
	cond := (self, o, opts) >> cond(o.args[1], self(o.args[2], opts), self(o.args[3], opts)),
	abs := (self, o, opts) >> abs(self(o.args[1], opts)),		
	logic_and := (self, o, opts) >> logic_and(self(o.args[1], opts), self(o.args[2], opts)),
	logic_or := (self, o, opts) >> logic_or(self(o.args[1], opts), self(o.args[2], opts)),
	gt  := (self, o, opts) >> gt(self(o.args[1], opts), self(o.args[2], opts)),
	lt  := (self, o, opts) >> lt(self(o.args[1], opts), self(o.args[2], opts)),
	geq  := (self, o, opts) >> geq(self(o.args[1], opts), self(o.args[2], opts)),
	leq  := (self, o, opts) >> leq(self(o.args[1], opts), self(o.args[2], opts)),
	min := (self, o, opts) >> min(self(o.args[1], opts), self(o.args[2], opts)),
	max := (self, o, opts) >> max(self(o.args[1], opts), self(o.args[2], opts)),
	
	nth := (self, o, opts) >> o,
	Value := (self, o, opts) >> o,		  
	var := (self, o, opts) >> o, 
	
	skip := (self, o, opts) >> o,	
	tcast := (self, o, opts) >> o,
	
	creturn := (self, o, opts) >> o,
	creturnCond := (self, o, opts) >> o,
	
	eq := (self, o, opts) >> eq(self(o.args[1], opts), self(o.args[2], opts)),
));

HCOLCodegen.IVArith := (self, o, y, x, opts) >> let(    
	#Generate non interval code
    cc := opts.codegen.OLCompose(o.child(1), y, x, opts),
	
	#Collect array of bools and make them into arrays of ints
	ba_vars := Filtered(FoldL(Collect(cc, var), (a,b)->When(not b.id in List(a, i->i.id), Concat([b],a), a), []), 
    	    e->ObjId(e.t) = TArray and e.t.base_t()=TBool),
    ba_nvars := List(ba_vars, c-> [c, var.fresh_t("U", TArray(TInt, c.t.size))] ),
    ba_svars := FoldL(ba_nvars, (b, a)->CopyFields(rec((a[1].id):= a[2]), b), rec()),
    ba_cc1 := decl(List(ba_nvars, c->c[2]), SubstVars(cc, ba_svars)),
	
	#Cast bools variables into ints but make sure that they are not part of the input parameters
	b_vars :=Unique(Collect(ba_cc1, @(1,var).cond(e->e.t = TBool))),
	b_local_vars := Difference(b_vars, opts.params),
	b_global_vars := Difference(b_vars, b_local_vars),	
	b_no_global := SubstBottomUp(ba_cc1, @(1,var).cond(e->e.t=TBool), f->let(Print(@(1).val.id, "\n"), 
							tcast(TInt, @(1).val))),
	
	#Cast pointers to bools into pointers to ints
	b_cc2 := b_no_global,
	
	#Convert boolean constants into ints
	b_cc3 := SubstBottomUp(b_cc2, @(1,Value).cond(e->e.t=TBool), 
        f->let(#Print(@(1).val, "\n"), 
			Cond(@(1).val=V_true,  V(1), 
			     @(1).val=V_false, V(0),
						   @(1).val))),
	
	#Collect array variables make them into arrays of intervals
    vars := Filtered(FoldL(Collect(b_cc3, var), (a,b)->When(not b.id in List(a, i->i.id), Concat([b],a), a), []), 
    	    e->ObjId(e.t) = TArray and e.t.base_t() in [TReal, TDouble, T_Real(32), T_Real(64)]),
    nvars := List(vars, c-> [c, var.fresh_t("U", TArray(TIVReal(c.t.base_t()), c.t.size))] ),
    svars := FoldL(nvars, (b, a)->CopyFields(rec((a[1].id):= a[2]), b), rec()),
    cc1 := decl(List(nvars, c->c[2]), SubstVars( cc, svars)),

	#Cast doubles and reals variables into intervals
    cc11 := SubstBottomUp(cc1, @(1,var).cond(e->e.t in [TReal, TDouble, T_Real(32), T_Real(64)]), f->tcast(opts.IVRealType, @(1).val)),

	#Cast pointers to doubles and reals into intervals
    cc2 := SubstBottomUp(cc11, [@(1,nth), @(2, var, e->ObjId(e.t) = TPtr and e.t.base_t() in [TReal, TDouble, T_Real(32), T_Real(64)]), @(3)], f->tcast(opts.IVRealType, @(1).val)),
	
	#Cast constants into intervals
    cc3 := SubstBottomUp(cc2, @(1,Value).cond(e->e.t in [TReal, TDouble, T_Real(32), T_Real(64)]), 
        f->let(tcast(opts.IVValueType, @(1).val))),

	result := ivenv(cc3),
	
	result2 := TypeUpdate(result, opts),
	
	result2
);

HCOLUnparser.RealEPS := (self,o,i,is) >> Print(Cond(o.args[1] = T_Real(64), "DBL_MIN", o.args[1] = T_Real(32), "FLT_MIN", "UNKNOWN_MIN"));
HCOLUnparser.RealMPS := (self,o,i,is) >> Print(Cond(o.args[1] = T_Real(64), "DBL_MAX", o.args[1] = T_Real(32), "FLT_MAX", "UNKNOWN_MAX"));
HCOLUnparser.ivenv := (self,o,i,is) >> self(chain(o.cmds), i, is);

HCOLUnparser.TIVReal := (self, t, vars, i, is) >> 	
		Print("interval_t ", self.infix(vars, ", ", i + is));
HCOLUnparser.TVect := (self, t, vars, i, is) >> Print("abc_interval_t ", self.infix(vars, ", ", i + is));





HCOLSSEUnparser.ivenv := (self,o,i,is) >> Print(Blanks(i), "{\n",
    Blanks(i+is), "unsigned _xm = _mm_getcsr();\n",
    Blanks(i+is), "_mm_setcsr(_xm & 0xffff0000 | 0x0000dfc0);\n",
    self(chain(o.cmds),i+is,is),
    Blanks(i+is), 
    Cond(IsBound(self.opts.compiler) and self.opts.compiler = "IntelC", "__asm nop;\n", 
        IsBound(self.opts.compiler) and self.opts.compiler = "GnuC", "asm volatile(\"\":::\"memory\");\n",
        "// BASIC BLOCK BARRIER\n"
    ),
    Blanks(i+is), "if (_mm_getcsr() & 0x0d) {\n",
    Blanks(i+2*is), "_mm_setcsr(_xm);\n",
	Blanks(i+2*is),
    Cond(self.opts.useCReturn, "return -1;\n", "Y[0] = -1;\n"),
    Blanks(i+is), "}\n",
    Blanks(i+is), "_mm_setcsr(_xm);\n",
    Blanks(i), "}\n");
	
HCOLSSEUnparser.RealEPS := HCOLUnparser.RealEPS;
HCOLSSEUnparser.RealMPS := HCOLUnparser.RealMPS;


Declare(ToIVArithBasic);

Class(ToIVArithBasic_Base, HierarchicalVisitor, rec(
    __call__ := meth(arg)
        local res;
        res := ApplyFunc(arg[1].visit, arg{[2..Length(arg)]});
        trace_log.addConversion(ObjId(arg[2]), arg[2], res, var);
       return res;
    end,
    func := (self, o, opts) >> let(Print("CONVERSION\n\n"), 
		func(o.ret, o.id, FoldL(o.params, (a, b)->Concat(a, When(IsBound(opts.state) and b=opts.state, [opts.ivstate], [b])), []), self(o.cmd, opts))),
    creturn := (self, o, opts) >> o,
	creturnCond := (self, o, opts) >> o,
    decl := (self, o, opts) >> let(
        ovars := Filtered(o.vars, e->ObjId(e.t) = TIVReal),
        svars := FoldR(ovars, (b,a)->CopyFields(rec((a.id):=var.fresh_t("u", TVect(T_Real(64), 2))), b), rec()),
        vars := Filtered(o.vars, e->ObjId(e.t) <> TIVReal)::List(Filtered(RecFields(svars), i->not i in SystemRecFields), i->svars.(i)),
        cmd := SubstVars(o.cmd, svars),
        decl(vars, self(cmd, opts))),
    chain := (self, o, opts) >> chain(List(o.cmds, i-> self(i, opts))),
    ivenv := (self, o, opts) >> ivenv(List(o.cmds, i-> ToIVArithBasic(i, opts))),
    loop := (self, o, opts) >> loop(o.var, o.range, self(o.cmd, opts)),
    nth := (self, o, opts) >> o,
	
    Value := (self, o, opts) >> let(
        When(ObjId(o.t) = TIVReal, 
          TVect(T_Real(64), 2).value([-o.v, o.v]), 
          o)),
		  
	skip := (self, o, opts) >> o,
	
	tcast := (self, o, opts) >> o,
	logic_and := (self, o, opts) >> o,
	logic_or := (self, o, opts) >> o,
	assign := (self, o, opts) >> o, 
));

Class(ToIVArithBasic, HierarchicalVisitor, rec(
    __call__ := meth(arg)
        local res;
        res := ApplyFunc(arg[1].visit, arg{[2..Length(arg)]});
        trace_log.addConversion(ObjId(arg[2]), arg[2], res, var);
       return res;
    end,
    func := (self, o, opts) >> let(Print("CONVERSION\n\n"), 
		func(o.ret, o.id, FoldL(o.params, (a, b)->Concat(a, When(IsBound(opts.state) and b=opts.state, [opts.ivstate], [b])), []), self(o.cmd, opts))),
    creturn := (self, o, opts) >> o,
	creturnCond := (self, o, opts) >> o,
    decl := (self, o, opts) >> let(
        ovars := Filtered(o.vars, e->ObjId(e.t) = TIVReal),
        svars := FoldR(ovars, (b,a)->CopyFields(rec((a.id):=var.fresh_t("u", TVect(T_Real(64), 2))), b), rec()),
        vars := Filtered(o.vars, e->ObjId(e.t) <> TIVReal)::List(Filtered(RecFields(svars), i->not i in SystemRecFields), i->svars.(i)),
        cmd := SubstVars(o.cmd, svars),
        decl(vars, self(cmd, opts))),
    chain := (self, o, opts) >> chain(List(o.cmds, i-> self(i, opts))),
    ivenv := (self, o, opts) >> ivenv(List(o.cmds, i-> self(i, opts))),
    loop := (self, o, opts) >> loop(o.var, o.range, self(o.cmd, opts)),
    nth := (self, o, opts) >> o,
	
    Value := (self, o, opts) >> let(
        When(ObjId(o.t) = TIVReal, 
          TVect(T_Real(64), 2).value([-o.v, o.v]), 
          o)),
		  
	skip := (self, o, opts) >> o,
	
	tcast := (self, o, opts) >> o,
   		
	logic_and := (self, o, opts) >> cond(eq(o.args[1],o.args[2]), o.args[1], mul(o.args[1], o.args[2])),
	logic_or := (self, o, opts) >> cond(logic_or(eq(o.args[1], 1), eq(o.args[2],1)), 1, min(o.args[1], o.args[2])),

    assign := (self, o, opts) >> let( 	  
	  Cond(
	    ObjId(o.exp) = var, 
			let(
				chain(
					assign(o.loc[1], tcast(o.loc[1].t,o.exp)),
					assign(o.loc[2], tcast(o.loc[2].t,o.exp))
				)				
			),			
	    ObjId(o.exp) = tcast and (o.exp.args[1] = TIVReal or o.exp.args[1] = TVect(T_Real(64), 2)),
				Cond(					
					o.exp.args[2].t = T_Real(32), 
						let(
							x0 := var.fresh_t("x", T_Real(64)), 
							x1 := var.fresh_t("x", T_Real(64)), 														
							decl([x0, x1], chain(
								self(assign([x0,x1], o.exp.args[2]), opts), 								
								assign(o.loc[1], x0+RealEPS(T_Real(32))),
								assign(o.loc[2], x1-RealEPS(T_Real(32)))
							))
						),
					IsDouble(o.exp.args[2]), 
						let(
							x0 := var.fresh_t("x", T_Real(64)), 
							x1 := var.fresh_t("x", T_Real(64)), 		
							decl([x0, x1], chain(
								self(assign([x0,x1], o.exp.args[2]), opts), 								
								assign(o.loc[1], x0),
								assign(o.loc[2], -x1)
							))
						),
					Error("Don't know how to convert <o.args[2]> to an interval.")),
		ObjId(o.exp) = lt and ForAll(o.exp.args, i->i.t = TIVReal or i.t = TVect(T_Real(64), 2)),
            let(
				x10 := var.fresh_t("x", T_Real(64)), 
				x11 := var.fresh_t("x", T_Real(64)), 
				x20 := var.fresh_t("x", T_Real(64)), 
				x21 := var.fresh_t("x", T_Real(64)), 				
                decl([x10, x11, x20, x21], chain(
					self(assign([x10, x11], o.exp.args[1]), opts),
					self(assign([x20, x21], o.exp.args[2]), opts),					
					assign(o.loc, tcast(TInt, cond(lt(x10, x21), V(1), cond(lt(x20,x11), V(0),V(-1)))))
                ))
            ),
		ObjId(o.exp) = gt and ForAll(o.exp.args, i->i.t = TIVReal or i.t = TVect(T_Real(64), 2)),
            let(x10 := var.fresh_t("x", T_Real(64)), 
				x11 := var.fresh_t("x", T_Real(64)), 
				x20 := var.fresh_t("x", T_Real(64)), 
				x21 := var.fresh_t("x", T_Real(64)), 				
                decl([x10, x11, x20, x21], chain(
					self(assign([x10, x11], o.exp.args[1]), opts),
					self(assign([x20, x21], o.exp.args[2]), opts),					
					assign(o.loc, tcast(TInt, cond(gt(x11, x20), V(1), cond(gt(x21, x10), V(0), V(-1)))))
                ))
            ),
	
		ObjId(o.exp) = add  and ForAll(o.exp.args, i->i.t = TIVReal or i.t = TVect(T_Real(64), 2)),
			let(x10 := var.fresh_t("x", T_Real(64)), 
				x11 := var.fresh_t("x", T_Real(64)), 
				x20 := var.fresh_t("x", T_Real(64)), 
				x21 := var.fresh_t("x", T_Real(64)), 				
				decl([x10, x11, x20, x21], chain(
					self(assign([x10, x11], o.exp.args[1]), opts),
					self(assign([x20, x21], o.exp.args[2]), opts),					
					assign(o.loc[1], add(x11, x21)),
					assign(o.loc[2], add(x10, x20)) 
				)) 
		  ),
		ObjId(o.exp) = sub  and ForAll(o.exp.args, i->i.t = TIVReal or i.t = TVect(T_Real(64), 2)),
			let(x10 := var.fresh_t("x", T_Real(64)), 
				x11 := var.fresh_t("x", T_Real(64)), 
				x20 := var.fresh_t("x", T_Real(64)), 
				x21 := var.fresh_t("x", T_Real(64)), 				
				decl([x10, x11, x20, x21], chain(
					self(assign([x10, x11], o.exp.args[1]), opts),
					self(assign([x20, x21], o.exp.args[2]), opts),
					assign(o.loc[1], sub(x11, x20)), 
					assign(o.loc[2], sub(x10, x21))
				)) 
			),
		ObjId(o.exp) = abs  and ForAll(o.exp.args, i->i.t = TIVReal or i.t = TVect(T_Real(64), 2)),
            let(				
				x10 := var.fresh_t("x", T_Real(64)), 
				x11 := var.fresh_t("x", T_Real(64)),
				x2 := var.fresh_t("x", T_Real(64)), 
				x3 := var.fresh_t("x", T_Real(64)),
                decl([x10, x11, x2, x3], chain(
					self(assign([x10, x11], o.exp.args[1]), opts),
					assign(x2, abs(x10)),
					assign(x3, abs(x11)),
					assign(o.loc[1], max(x2, x3)),
					assign(o.loc[2], min(x2, x3))
                ))
            ),		
		assign(o.loc, self(o.exp, opts)) 
    )),		
));


Class(ToIVArithSSE, HierarchicalVisitor, rec(
    __call__ := meth(arg)
        local res;
        res := ApplyFunc(arg[1].visit, arg{[2..Length(arg)]});
        trace_log.addConversion(ObjId(arg[2]), arg[2], res, var);
       return res;
    end,
    func := (self, o, opts) >> let(#Print("CONVERSION\n\n"), 
		func(o.ret, o.id, FoldL(o.params, (a, b)->Concat(a, When(IsBound(opts.state) and b=opts.state, [opts.ivstate], [b])), []), self(o.cmd, opts))),
    creturn := (self, o, opts) >> o,
	creturnCond := (self, o, opts) >> o,
    decl := (self, o, opts) >> let(
        ovars := Filtered(o.vars, e->ObjId(e.t) = TIVReal),
        svars := FoldR(ovars, (b,a)->CopyFields(rec((a.id):=var.fresh_t("u", TVect(T_Real(64), 2))), b), rec()),
        vars := Filtered(o.vars, e->ObjId(e.t) <> TIVReal)::List(Filtered(RecFields(svars), i->not i in SystemRecFields), i->svars.(i)),
        cmd := SubstVars(o.cmd, svars),
        decl(vars, self(cmd, opts))),
    chain := (self, o, opts) >> chain(List(o.cmds, i-> self(i, opts))),
    ivenv := (self, o, opts) >> ivenv(List(o.cmds, i-> self(i, opts))),
    loop := (self, o, opts) >> loop(o.var, o.range, self(o.cmd, opts)),
    nth := (self, o, opts) >> o,
    Value := (self, o, opts) >> let(
        When(ObjId(o.t) = TIVReal, 
          TVect(T_Real(64), 2).value([-o.v, o.v]), 
          o)),
    var := (self, o, opts) >> o,
	skip := (self, o, opts) >> o,
    tcast := (self, o, opts) >> Cond(
        IsDouble(o.args[2]), vpack(-o.args[2], o.args[2]),	
	IsValue(o.args[2]), TVect(T_Real(64), 2).value([-o.args[2].v, o.args[2].v]),
        o.args[2].t = T_Real(32), addsub_2x64f(vcvt_64f32f(vdup(RealEPS(T_Real(32)), 4)), vcvt_64f32f(vdup(o.args[2], 4))),
        o.args[2].t = T_Real(64), addsub_2x64f(vdup(RealEPS(T_Real(64))+RealEPS(T_Real(64)), 2), vdup(o.args[2], 2)),
	o.args[2].t = TIVReal(T_Real(64)),  TVect(T_Real(64),2).value(o.args[2]),
        Error("Don't know how to convert <o.args[2]> to an interval.")),
		
	logic_and := (self, o, opts) >> cond(eq(o.args[1],o.args[2]), o.args[1], mul(o.args[1], o.args[2])),
	logic_or := (self, o, opts) >> cond(logic_or(eq(o.args[1], 1), eq(o.args[2],1)), 1, min(o.args[1], o.args[2])),

    testc_4x32i:= (self, o, opts) >> o, 

    assign := (self, o, opts) >> Cond(
	    ObjId(o.exp) = add and (o.loc.t = TIVReal or o.loc.t = TVect(T_Real(64), 2)),
		  let(
			x1 := var.fresh_t("x", TVect(T_Real(64), 2)), x2 := var.fresh_t("x", TVect(T_Real(64), 2)),
			decl([x1, x2], chain(
				comment("addition"),
				self(assign(x1, o.exp.args[1]), opts), 
				self(assign(x2, o.exp.args[2]), opts), 
				assign(o.loc, add(x1, x2)) ) ) 
		  ),
		ObjId(o.exp) = sub and (o.loc.t = TIVReal or o.loc.t = TVect(T_Real(64), 2)),
		  let(
			x1 := var.fresh_t("x", TVect(T_Real(64), 2)), x2 := var.fresh_t("x", TVect(T_Real(64), 2)),
			decl([x1, x2], chain(
				comment("sub"),
				self(assign(x1, o.exp.args[1]), opts), 
				self(assign(x2, o.exp.args[2]), opts), 
				assign(o.loc, add(x1, vushuffle_2x64f(x2, vparam([2,1])))) ) ) 
		  ),
        ObjId(o.exp) = mul and (o.loc.t = TIVReal or o.loc.t = TVect(T_Real(64), 2)),
            let(u := var.fresh_t("x", TVect(T_Real(64), 2)), a := var.fresh_t("x", TVect(T_Real(64), 2)), 
                b := var.fresh_t("x", TVect(T_Real(64), 2)), c := var.fresh_t("x", TVect(T_Real(64), 2)),
                x1 := var.fresh_t("x", TVect(T_Real(64), 2)), x2 := var.fresh_t("x", TVect(T_Real(64), 2)),
                decl([u, a, b, c, x1, x2], chain(
					comment("mul"),
					self(assign(x1, o.exp.args[1]), opts),
					self(assign(x2, o.exp.args[2]), opts),
                    assign(u, addsub_2x64f(TVect(T_Real(64), 2).zero(), x1)),
                    assign(a, mul(u, x2)),
                    assign(b, mul(vushuffle_2x64f(u, vparam([2,1])), x2)),
                    assign(c, neg(min(a, b))),
                    assign(o.loc, add(max(max(a, b), vushuffle_2x64f(c, vparam([2,1]))), vdup(RealEPS(T_Real(64)), 2)))
                ))
            ),
        ObjId(o.exp) = abs and (o.loc.t = TIVReal or o.loc.t = TVect(T_Real(64), 2)),
            let(u := var.fresh_t("x", TVect(T_Real(64), 2)), x1 := var.fresh_t("x", TVect(T_Real(64), 2)),
                decl([u, x1], chain(
					comment("abs"),	
                    self(assign(x1, o.exp.args[1]), opts),
                    assign(u, vushuffle_2x64f(x1, vparam([2,1]))),
                    assign(o.loc, vshuffle_2x64f(min(x1, u), max(x1, u), vparam([1,2])))
                ))
            ),
		ObjId(o.exp) = pow and (o.loc.t = TIVReal or o.loc.t = TVect(T_Real(64), 2)) and IsValue(o.exp.args[2]) and o.exp.args[2].v = 2, 
			let( x1 := var.fresh_t("x", TVect(T_Real(64), 2)),
				decl([x1], chain(
					self(assign(x1, mul(o.exp.args[1],o.exp.args[1])), opts),
					assign(o.loc, x1)
				))
			),
		ObjId(o.exp) = pow and (o.loc.t = TIVReal or o.loc.t = TVect(T_Real(64), 2)) and IsValue(o.exp.args[2]) and IsInt(o.exp.args[2].v) and o.exp.args[2] > 2, 
			let( x1 := var.fresh_t("x", TVect(T_Real(64), 2)),
				decl([x1], chain(
					self(assign(x1, mul(o.exp.args[1], pow(o.exp.args[1],o.exp.args[2].v-1))), opts),
					assign(o.loc, x1)
				))
			),							
			
		ObjId(o.exp) = div and (o.loc.t = TIVReal or o.loc.t = TVect(T_Real(64), 2)) and not IsValue(o.exp.args[1]),		
			let( 
			Print("DIVISION - PART 1\n"),
			  x1 := var.fresh_t("x", TVect(T_Real(64), 2)),			 
			  decl([x1], chain(
				self(assign(x1, mul(o.exp.args[1], 1.0/o.exp.args[2])), opts),
				assign(o.loc, x1)
			  ))
			),
			
		ObjId(o.exp) = div and <#o.loc.t = TIVReal or o.loc.t = TVect(T_Real(64), 2)) and #>IsValue(o.exp.args[1]),
			let( 			
				x1 := var.fresh_t("x", TVect(T_Real(64), 2)),			 
				decl([x1], chain(				
					assign(x1, vdiv_2x64f(TVect(T_Real(64), 2).value([-o.exp.args[1].v,o.exp.args[1].v]), o.exp.args[2])),
					assign(o.loc, vshuffle_2x64f(x1, x1, vparam([2,1])))
				))
			),
		ObjId(o.exp) = neg and (o.loc.t = TIVReal or o.loc.t = TVect(T_Real(64), 2)),
		    let(x1 := var.fresh_t("x", TVect(T_Real(64), 2)),x2 := var.fresh_t("x", TVect(T_Real(64), 2)),
				decl([x1], chain(
					self(assign(x1, TVect(T_Real(64), 2).value([0,0]), opts)),
					self(assign(x2, sub(x1, o.exp.args[1])), opts),
					assign(o.loc, x2)
				))
			),			
        ObjId(o.exp) = max and (o.loc.t = TIVReal or o.loc.t = TVect(T_Real(64), 2)),
            let(x1 := var.fresh_t("x", TVect(T_Real(64), 2)), x2 := var.fresh_t("x", TVect(T_Real(64), 2)),
                decl([x1, x2], chain(					
                    self(assign(x1, o.exp.args[1]), opts),
                    self(assign(x2, o.exp.args[2]), opts),
                    assign(o.loc, vshuffle_2x64f(min(x1, x2), max(x1, x2), vparam([1, 2])))
                ))
            ),		 
         ObjId(o.exp) = min and (o.loc.t = TIVReal or o.loc.t = TVect(T_Real(64), 2)),
            let(x1 := var.fresh_t("x", TVect(T_Real(64), 2)), x2 := var.fresh_t("x", TVect(T_Real(64), 2)),
                decl([x1, x2], chain(
                    self(assign(x1, o.exp.args[1]), opts),
                    self(assign(x2, o.exp.args[2]), opts),
                    assign(o.loc, vshuffle_2x64f(max(x1, x2), min(x1, x2), vparam([1, 2])))
                ))
            ),		
        ObjId(o.exp) = geq <#and (o.loc.t = TBool or o.loc.t = TInt)#> and ForAll(o.exp.args, i->i.t = TIVReal or i.t = TVect(T_Real(64), 2)),
            let(x1 := var.fresh_t("x", TVect(T_Real(64), 2)), x2 := var.fresh_t("x", TVect(T_Real(64), 2)), u := var.fresh_t("x", TVect(T_Real(64), 2)), 
                decl([x1, x2, u], chain(
					comment("geq"),	
                    assign(x1, addsub_2x64f(TVect(T_Real(64), 2).zero(), self(o.exp.args[1], opts))),
                    assign(x2, addsub_2x64f(TVect(T_Real(64), 2).zero(), self(o.exp.args[2], opts))),
                    assign(u, cmpge_2x64f(x1, vushuffle_2x64f(x2, vparam([2, 1])))),
                    assign(o.loc, sub(
                        testc_4x32i(tcast(TVect(T_Int(32), 4), u), vhex(Replicate(4, "0xffffffff"))), 
                        testnzc_4x32i(tcast(TVect(T_Int(32), 4), u), vhex(Replicate(4, "0xffffffff")))))
                ))
            ),
        ObjId(o.exp) = leq <#and o.loc.t = TBool#> and ForAll(o.exp.args, i->i.t = TIVReal or i.t = TVect(T_Real(64), 2)),
            let(x1 := var.fresh_t("x", TVect(T_Real(64), 2)), x2 := var.fresh_t("x", TVect(T_Real(64), 2)), u := var.fresh_t("x", TVect(T_Real(64), 2)),
                decl([x1, x2, u], chain(
                    assign(x1, addsub_2x64f(TVect(T_Real(64), 2).zero(), self(o.exp.args[1], opts))),
                    assign(x2, addsub_2x64f(TVect(T_Real(64), 2).zero(), self(o.exp.args[2], opts))),
                    assign(u, cmple_2x64f(x1, vushuffle_2x64f(x2, vparam([2, 1])))),
                    assign(o.loc, sub(
                        testc_4x32i(tcast(TVect(T_Int(32), 4), u), vhex(Replicate(4, "0xffffffff"))), 
                        testnzc_4x32i(tcast(TVect(T_Int(32), 4), u), vhex(Replicate(4, "0xffffffff")))))
                ))
            ),
		ObjId(o.exp) = gt <#and (o.loc.t = TBool or o.loc.t = TInt)#> and ForAll(o.exp.args, i->i.t = TIVReal or i.t = TVect(T_Real(64), 2)),
            let(x1 := var.fresh_t("x", TVect(T_Real(64), 2)), x2 := var.fresh_t("x", TVect(T_Real(64), 2)), u := var.fresh_t("x", TVect(T_Real(64), 2)), 
                decl([x1, x2, u], chain(
                    assign(x1, addsub_2x64f(TVect(T_Real(64), 2).zero(), self(o.exp.args[1], opts))),
                    assign(x2, addsub_2x64f(TVect(T_Real(64), 2).zero(), self(o.exp.args[2], opts))),
                    assign(u, cmpgt_2x64f(x1, vushuffle_2x64f(x2, vparam([2, 1])))),
                    assign(o.loc, sub(
                        testc_4x32i(tcast(TVect(T_Int(32), 4), u), vhex(Replicate(4, "0xffffffff"))), 
                        testnzc_4x32i(tcast(TVect(T_Int(32), 4), u), vhex(Replicate(4, "0xffffffff")))))
                ))
            ),
        ObjId(o.exp) = lt <#and o.loc.t = TBool#> and ForAll(o.exp.args, i->i.t = TIVReal or i.t = TVect(T_Real(64), 2)),
            let(x1 := var.fresh_t("x", TVect(T_Real(64), 2)), x2 := var.fresh_t("x", TVect(T_Real(64), 2)), u := var.fresh_t("x", TVect(T_Real(64), 2)),
                decl([x1, x2, u], chain(
                    assign(x1, addsub_2x64f(TVect(T_Real(64), 2).zero(), self(o.exp.args[1], opts))),
                    assign(x2, addsub_2x64f(TVect(T_Real(64), 2).zero(), self(o.exp.args[2], opts))),
                    assign(u, cmplt_2x64f(x1, vushuffle_2x64f(x2, vparam([2, 1])))),
                    assign(o.loc, sub(
                        testc_4x32i(tcast(TVect(T_Int(32), 4), u), vhex(Replicate(4, "0xffffffff"))), 
                        testnzc_4x32i(tcast(TVect(T_Int(32), 4), u), vhex(Replicate(4, "0xffffffff")))))
                ))
            ),				
		ObjId(o.exp) = eq,
			let(Error("Eq not implemented for interval arithmetic.")),
		ObjId(o.exp) = neq,
			let(Error("Neq not implemented for interval arithmetic.")),
			
        assign(o.loc, self(o.exp, opts))
    ),								   	
    mul := (self, o, opts) >> ApplyFunc(ObjId(o), List(o.args, i-> self(i, opts))),
    abs := (self, o, opts) >> ApplyFunc(ObjId(o), List(o.args, i-> self(i, opts))),
    max := (self, o, opts) >> ApplyFunc(ObjId(o), List(o.args, i-> self(i, opts))),
	add := (self, o, opts) >> ApplyFunc(ObjId(o), List(o.args, i-> self(i, opts))),
	sub := (self, o, opts) >> ApplyFunc(ObjId(o), List(o.args, i-> self(i, opts))),
    geq := (self, o, opts) >> ApplyFunc(ObjId(o), List(o.args, i-> self(i, opts))),
    leq := (self, o, opts) >> ApplyFunc(ObjId(o), List(o.args, i-> self(i, opts))),
	gt  := (self, o, opts) >> ApplyFunc(ObjId(o), List(o.args, i-> self(i, opts))),
    lt  := (self, o, opts) >> ApplyFunc(ObjId(o), List(o.args, i-> self(i, opts))),
	pow := (self, o, opts) >> ApplyFunc(ObjId(o), List(o.args, i-> self(i, opts))),
	div := (self, o, opts) >> ApplyFunc(ObjId(o), List(o.args, i-> self(i, opts))),
));

HCOLSSEUnparser.TIVReal := (self, t, vars, i, is) >> Print("__m128d ", self.infix(vars, ", ", i + is));

CoSynthesizeStrategies.IVArithSSE := [ (t, opts) -> RandomRuleTree(t, opts), 
        (rt, opts) -> SPLRuleTree(rt),
        (s, opts) -> SumsSPL(s, opts),
        (s, opts) -> Rewrite(s, [RulesSumsHCOLv2a, RulesTerminateReductionHCOL, RulesSumsHCOLv2b], opts),
        (s, opts) -> HCOLProof_Codegen(s, opts),
        (c, opts) -> Rewrite(c, RulesCodeUnrollHACMIVArth, opts),
        (c, opts) -> HCOLProof_CodeConversion(c, ToIVArithSSE, opts),
        (c, opts) -> Rewrite(c, RulesCodeUnrollHACMIVArthType, opts) ];

		
CoSynthesizeStrategies.IVArithBasic := [ (t, opts) -> RandomRuleTree(t, opts), 
        (rt, opts) -> SPLRuleTree(rt),
        (s, opts) -> SumsSPL(s, opts),
        (s, opts) -> Rewrite(s, [RulesSumsHCOLv2a, RulesTerminateReductionHCOL, RulesSumsHCOLv2b], opts),
        (s, opts) -> HCOLProof_Codegen(s, opts),
        (c, opts) -> Rewrite(c, RulesCodeUnrollHACMIVArth, opts),
        (c, opts) -> HCOLProof_CodeConversion(c, ToIVArithBasic_Base, opts),
        (c, opts) -> Rewrite(c, RulesCodeUnrollHACMIVArth, opts) ];		
		
HCOLSSEUnparser.addsub_2x64f := (self, o, i, is) >> Checked(Length(o.args) = 2,
        CondPat(o,
           [addsub_2x64f, @TReal, @TVect], self(addsub_2x64f(vdup(o.args[1],o.t.size), o.args[2]), i, is),
           [addsub_2x64f, @TVect, @TReal], self(addsub_2x64f(o.args[1], vdup(o.args[2], o.t.size)), i, is),
           [addsub_2x64f, @TInt,  @TVect], self(addsub_2x64f(vdup(_toReal(o.args[1]), o.t.size), o.args[2]), i, is),
           [addsub_2x64f, @TVect, @TInt],  self(addsub_2x64f(o.args[1], vdup(_toReal(o.args[2]), o.t.size)), i, is),
           [addsub_2x64f, @TVect, @TVect], self.printf("_mm_addsub_pd($1, $2)", o.args),
           [addsub_2x64f, @TVect, @(1).cond(e->e.t=TIVReal)], self.printf("_mm_addsub_pd($1, $2)", o.args),
           [addsub_2x64f, @(1).cond(e->e.t=TIVReal), @TVect], self.printf("_mm_addsub_pd($1, $2)", o.args),
           Error("Don't know how to unparse <o>. Unrecognized type combination")
    ));

HCOLSSEUnparser.max := (self, o, i, is) >> let(n := Length(o.args), When(
	IsVecT(o.t) and n >2, self.printf("_mm_max_$1($2, $3)", [self.ctype_suffix(o.t, _isa(self)), o.args[1],
		ApplyFunc(max, Drop(o.args, 1))]), 
	CondPat(o, 
		[max, @TVect, @TVect], self.prefix("_mm_max_" :: self.ctype_suffix(o.t, _isa(self)),o.args),
	    [max, @TVect, @(1).cond(e->e.t=TIVReal)], self.printf("_mm_max_pd($1, $2)", o.args),
        [max, @(1).cond(e->e.t=TIVReal), @TVect], self.printf("_mm_max_pd($1, $2)", o.args),
		Inherited(o, i, is))
));

HCOLSSEUnparser.min := (self, o, i, is) >> let(
	CondPat(o, 
		[min, @TVect, @TVect], self.prefix("_mm_min_" :: self.ctype_suffix(o.t, _isa(self)),o.args),
	    [min, @TVect, @(1).cond(e->e.t=TIVReal)], self.printf("_mm_min_pd($1, $2)", o.args),
        [min, @(1).cond(e->e.t=TIVReal), @TVect], self.printf("_mm_min_pd($1, $2)", o.args),
		Inherited(o, i, is))
);


geq.computeType := self >> TBool;
leq.computeType := self >> TBool;	
eq.computeType := self >> TBool;
pow.computeType := (self) >> self.args[1].t;
neq.computeType := (self) >> TBool;
			
min.computeType := self >> let(
		types := List(self.args, e->e.t),
		When(Length(Collect(types, TIVReal))>0, 
			TIVReal(UnifyTypes(List(Collect(types, TIVReal), i->i.t))),   <# TVect(T_Real(64),2),  #>
			UnifyTypes(List(self.args, x->x.t)))
	);
max.computeType := self >> let(
		types := List(self.args, e->e.t),
		When(Length(Collect(types, TIVReal))>0, 
			TIVReal(UnifyTypes(List(Collect(types, TIVReal), i->i.t))),   <# TVect(T_Real(64),2),  #>
			UnifyTypes(List(self.args, x->x.t)))
	);

	
VecExp.computeType := self >> let(
        t       := self.args[1].t,
        deref_t := When(IsPtrT(t), t.t, t),
        el_t    := Cond(IsVecT(deref_t), deref_t.t, deref_t),
	test    := Cond(el_t = TIVReal, el_t.t, el_t),
        TVect(test, self.v));

add.computeType := meth(self)
	    local len, t, ptr_args, other_args, sum;
	    len := Length(self.args);
	    if   len=0  then return TInt;
	    elif len=1  then return self.args[1].t;
	    else
            [ptr_args, other_args] := SplitBy(self.args, x->IsPtrT(x.t) or IsArrayT(x.t));
            if Length(ptr_args)=0 then
	       if (self.args[1].t = TIVReal or self.args[2].t = TIVReal) then
	         return TIVReal(T_Real(64));
	       else
	         return UnifyTypesL(self.args);
               fi;
            elif Length(ptr_args)=1 then
                sum := Sum(other_args);
                if other_args<>[] and not IsIntT(sum.t) then Error("Can't add non-integer to a pointer"); fi;
		   return self._ptrPlusOfs(ptr_args[1].t, sum);
            elif Length(other_args)=0 then
                return self._addPtrT(ptr_args);
            else
                return Error("Addition of more than one pointer and integers is not defined");
            fi;
	    fi;
    end;
	
sub.computeType := meth(self)
	    local len, t, ptr_args, other_args, sum;
	    len := Length(self.args);
	    if   len=0  then return TInt;
	    elif len=1  then return self.args[1].t;
	    else
            [ptr_args, other_args] := SplitBy(self.args, x->IsPtrT(x.t) or IsArrayT(x.t));
            if Length(ptr_args)=0 then
	       if (self.args[1].t = TIVReal or self.args[2].t = TIVReal) then
	         return TIVReal(T_Real(64));
	       else
	         return UnifyTypesL(self.args);
               fi;
            elif Length(ptr_args)=1 then
                sum := Sum(other_args);
                if other_args<>[] and not IsIntT(sum.t) then Error("Can't add non-integer to a pointer"); fi;
		   return self._ptrPlusOfs(ptr_args[1].t, sum);
            elif Length(other_args)=0 then
                return self._addPtrT(ptr_args);
            else
                return Error("Addition of more than one pointer and integers is not defined");
            fi;
	    fi;
    end;


mul.computeType := meth(self)
        local len, t, ptr_t, ptr_args, other_args, prod, args;
	args := self.args;

	len := Length(args);
	if   len=0  then return TInt;
	elif len=1  then return args[1].t;
	else
	    [ptr_args, other_args] := SplitBy(args, x->IsPtrT(x.t));
	    if Length(ptr_args)=0 then
	        if (self.args[1].t = TIVReal or self.args[2].t = TIVReal) then
  		  return TIVReal(T_Real(64));
		else
		  return UnifyTypesL(args);
		fi;
	    elif Length(ptr_args) > 1 then Error("Can't multiply pointers");
	    else
		prod := Product(other_args);
		if other_args<>[] and not IsIntT(prod.t) then Error("Can't multiply a pointer by a non-integer"); fi;
		return  self._ptrMul(ptr_args[1].t, prod);
	    fi;
	fi;
    end;
	
div.computeType := self >> When(self.args[1].t = TIVReal or self.args[2].t = TIVReal, TIVReal(T_Real(64)), UnifyTypes(List(self.args, x->x.t)));
	
TempArrayType := (child, y, x, index) ->
let(When(IsBound(child.a.t_in), child.a.t_in[index], 
		let( X := Flat([x])[1], Y:= Flat([y])[1],
			Cond(
				IsBound(X.t.t) and X.t.t = TComplex, 		TComplex,
				IsBound(Y.t.t) and Y.t.t = TComplex, 		TComplex,
				ObjId(child) = ISumReduction, 				When(IsRec(child.idval), child.idval.t, TReal),
				ObjId(child) = PointWise, 					child.op.expr.t,
				X.t.t))));
TempArray := (y, x, child) -> let(cols := Flat([ Cols(child) ]),
	newType := TempArrayType(child, y, x, 1),
      StripList(
        List([ 1 .. Length(cols) ], (i) -> TempVec(TArray(TempArrayType(child,
               y, x, i), cols[i])))) );	
	
	

				
