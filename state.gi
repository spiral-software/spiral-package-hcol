
# Copyright 2018-2019, Carnegie Mellon University
# See LICENSE for details

Class(TState, VStack, rec(
 dims := self >> [0, FoldL(self._children,(a,b)->When(not IsSymbolic(b.dims()[2]), Max2(a,b.dims()[2]), a), 0) ],
 isCommand := true
));

HCOLSumsGen.TState := (self, o, opts) >> let(
      ch := o.children(),      
      ApplyFunc(TState, List([1..Length(ch)], i->OLCompose(
        ScatHUnion(Rows(o), Rows(ch[i]),  Sum(List(ch{[1..i-1]}, child->child.dims()[1])), 1),
	self(ch[i], opts)
      )))
    );

HCOLCodegen.TState := (self, o, y, x, opts) >> List(o.children(), c -> self(c, opts.state, x, opts));

