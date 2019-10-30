
# Copyright 2018-2019, Carnegie Mellon University
# See LICENSE for details

_HCOLProof_apply := (R, nt, children, nonterms) -> Checked(IsRule(R), IsSPL(nt),
    When(IsNewRule(R),
     R.apply(nt, children, nonterms),
     When(NumGenArgs(R.rule)=2,
          R.rule(nt.params, children),
          R.rule(nt.params, children, nonterms)))
);

HCOLProof_Codegen := function(ss, opts) 
    local c;
    trace_log.beginStage("Sigma-SPL","icode", ss);    
    c := opts.funcgen.generate(ss, opts);
    trace_log.endStage("Sigma-SPL","icode", c);
    return c;
end;

HCOLProof_CodeConversion := function(c, visitor, opts) 
    local c2;
    # dead code?
    trace_log.beginStage("icode","icode", c);    
    c2 := visitor(c, opts);
    trace_log.beginStage("icode","icode", c2);
    return c2;
end;
