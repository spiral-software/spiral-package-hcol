
# Copyright 2018-2019, Carnegie Mellon University
# See LICENSE for details


Class(SIMDchain, chain);

update_opts_params:= function(opts, new_param)
   opts.params := opts.params::[new_param];
end;

update_opts_includes:= function(opts, new_param)
   opts.includes := opts.includes::[new_param];
end;

Class(HCOLFuncGen, rec(
    generate := (self, ss, opts) >>  let(
          err_chk := When(opts.errorCheck,
            let( x:= var.fresh_t("x", T_Real(32)), j := Ind(1),
                 ch := List(Filtered(opts.params, v->v.t in [T_Real(32), T_Real(64)]),
                                        vv-> PointWise(1, Lambda([x, j], cond(isinf(vv), 1, cond(isnan(vv), 2, 0))))),   
                 n := Length(ch),
                 t :=
                 OLCompose(
                    VStack(
                        Reduction(n, (a, b)->add(a, b), V(0), False),
                        I(n)
                    ),
                    VStack(    ch )
                 ),
                 tt := Rewrite(SumsSPL(t, opts), [RulesSumsHCOL, RulesTerminateReductionHCOL, RulesSumsHCOL], opts),
                 rtn_var := var("err", TPtr(TBool)), rtn := var("err_rtn", TBool),
                 update_opts_params(opts, rtn_var),
                 update_opts_includes(opts, "<math.h>"),                  
                 decl([rtn],
                    chain(
                      SubstBottomUp(opts.codegen.OLCompose(tt, rtn_var, self.getX(opts), opts),
                                    [nth, @(4, var, e->e.id = rtn_var.id), @(5, Value, e->e.v=0)], e->rtn),
                      creturnCond(neq(rtn, 0), -2)
                 ))),
            chain([])),
       
          code := opts.codegen.(ss.name)(ss, self.getY(opts), self.getX(opts), opts),
         
          finalCode := When(opts.useCReturn,            
                let( w:= var.fresh_t("w", self.getRetType(opts)),               
                     decl([w],                  
                        chain(
                            When(opts.errorCheck, err_chk, chain([])),
                            SIMDchain(
                                SubstBottomUp(code,
                                    [nth, @(2, var, e->e.id = self.getY(opts).id),
                                          @(3, Value, e->e.v=0)], e->w),
                               creturn(w))))),
             SIMDchain(err_chk, code)),
             
        func(self.getRetType(opts), "transform", self.getParams(finalCode, opts), finalCode)) ,
     
     
        getParams := (self, fc, opts) >> let(
       
            y := self.getY(opts), x := self.getX(opts),
            usedX := Length(Collect(fc, @(1, var, e->e.id=x.id)))>0,           
            Cond(
                opts.useCReturn and not usedX,       opts.params,
                not opts.useCReturn and not usedX,   [y]::opts.params,
                opts.useCReturn and usedX,           [x]::opts.params,
                not opts.useCReturn and usedX,       [y, x]::opts.params
        )
    ),
    getRetType := (self, opts) >> When(opts.useCReturn, opts.YType.t, TVoid),
    getX :=  (self, opts) >> CopyFields(X, rec(t:=opts.XType)),
    getY :=  (self, opts) >> CopyFields(Y, rec(t:=opts.YType))
));
