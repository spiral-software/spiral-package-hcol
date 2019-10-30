
# Copyright 2018-2019, Carnegie Mellon University
# See LICENSE for details

TempArrayType := (child, y, x, index) ->
let(When(IsBound(child.a.t_in), child.a.t_in[index], 
		let( X := Flat([x])[1], Y:= Flat([y])[1],
			Cond(
				IsBound(X.t.t) and X.t.t = TComplex, 		TComplex,
				IsBound(Y.t.t) and Y.t.t = TComplex, 		TComplex,
				ObjId(child) = ISumReduction, 				child.idval.t,
				ObjId(child) = PointWise, 					child.op.expr.t,
				X.t.t))));
TempArray := (y, x, child) -> let(cols := Flat([ Cols(child) ]),
	newType := TempArrayType(child, y, x, 1),
    StripList(
      List([ 1 .. Length(cols) ], (i) -> TempVec(TArray(TempArrayType(child,
               y, x, i), cols[i])))) );	
	