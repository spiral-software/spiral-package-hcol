
# Copyright 2018-2019, Carnegie Mellon University
# See LICENSE for details

Class(FloatMixin, rec(
    XType := TPtr(T_Real(32)), precision := "single", TRealCtype := "float")
);

Class(DoubleMixin, rec(
    XType := TPtr(T_Real(64)), precision := "double", TRealCtype := "double")
);


Class(CoSynthesizeStrategies, rec(
    C_opt := [ (t, opts) -> RandomRuleTree(t, opts), 
        (rt, opts) -> SPLRuleTree(rt),
        (s, opts) -> SumsSPL(s, opts),
        (s, opts) -> Rewrite(s, [RulesSumsHCOL, RulesTerminateReductionHCOL, RulesSumsHCOL], opts),
        (s, opts) -> HCOLProof_Codegen(s, opts),
        (c, opts) -> Rewrite(c, RulesCodeUnrollHCOL, opts),
		(c, opts) -> Rewrite(c, RulesTypeHCOL, opts)		],
    C_opt_useAbsMax := [ (t, opts) -> RandomRuleTree(t, opts),
		(rt, opts) -> SPLRuleTree(rt),
		(s, opts) -> SumsSPL(s, opts),
		(s, opts) -> Rewrite(s, [RulesSumsHCOL], opts),
		(s, opts) -> Rewrite(s, [RulesSumsHCOL, RulesTerminateReductionHCOL, RulesSumsHCOL], opts),
		(s, opts) -> HCOLProof_Codegen(s, opts),
		(c, opts) -> Rewrite(c, RulesCodeUnrollHCOLuseAbsMaxSR, opts) ],
    C_raw := [ (t, opts) -> RandomRuleTree(t, opts), 
        (rt, opts) -> SPLRuleTree(rt),
        (s, opts) -> SumsSPL(s, opts),
        (s, opts) -> Rewrite(s, [RulesSumsHCOL, RulesTerminateReductionHCOL, RulesSumsHCOL], opts),
        (s, opts) -> HCOLProof_Codegen(s, opts) ],
    C_sim := [        (s, opts) -> SumsSPL(s, opts),
        (s, opts) -> Rewrite(s, [RulesSumsHCOL, RulesTerminateReductionHCOL, RulesSumsHCOL], opts),
        (s, opts) -> HCOLProof_Codegen(s, opts),
	(c, opts) -> Rewrite(c, RulesCodeUnrollHCOL, opts) ],
	no_opt := [ (t, opts) -> RandomRuleTree(t, opts), 
        (rt, opts) -> SPLRuleTree(rt),
        (s, opts) -> SumsSPL(s, opts),
        (s, opts) -> Rewrite(s, [RulesSumsHCOL, RulesTerminateReductionHCOL, RulesSumsHCOL], opts),
        (s, opts) -> HCOLProof_Codegen(s, opts) ]
));
    

Class(HCOLopts, rec(
    getOpts := meth(arg)
        local opts;
       
        opts := CopyFields(SpiralDefaults, 
            rec(
                codegen := HCOLCodegen, 
                sumsgen := HCOLSumsGen, 
                params := [],
                includes := [], 
                unparser := HCOLUnparser,
                operations := rec(Print := (s) -> Print("<HCOL options"::When(Length(arg)>1 and IsBound(arg[2].name), ", "::arg[2].name, "")::">")),
                funcgen := HCOLFuncGen,
                useCReturn := false, 
				errorCheck := false,
                YType := TPtr(TInt),
                csStrategy := CoSynthesizeStrategies.C_opt
            ), 
            When(Length(arg)=2, arg[2]));
        return opts;
    end
));


