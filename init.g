
# Copyright 2018-2019, Carnegie Mellon University
# See LICENSE for details

_unwrapVec := vec -> When(IsList(vec), vec, List(vec.v, _unwrap));
_unwrapMat := mat-> List(mat.v, _unwrapVec);
_make1DFData := lst -> FData(Dat1d(TDouble, Length(lst)).setValue(V(List(lst, i->V(i))))); 
_make2DFData := mat -> FData(Dat2d(TDouble, Rows(mat), Cols(mat)).setValue(V(List(mat, i->V(List(i, j->V(j)))))));
_make3DFData := tens -> FData(Dat3d(TDouble, Length(tens), Rows(tens[1]), Cols(tens[1])).setValue(V(List(tens, mat->V(List(mat, i->V(List(i, j->V(j)))))))));

_make1DFDataVec := (_lst, vlen) -> let(lst := List([0..Length(_lst)/vlen-1], i->List([0..vlen-1], j->_lst[vlen*i+j+1])), 
    FData(Dat1d(TVect(TDouble, vlen), Length(lst)).setValue(
    Value(TArray(TVect(TDouble, vlen), Length(lst)), List(lst, i->Value(TVect(TDouble, vlen), List(i, j->V(j)))))))); 
_make2DFDataColVec := (m, vlen) -> let(
    mat := List([0..Length(m)/vlen-1], (k)->List([1..Length(m[1])], (i)->List([0..vlen-1], (j)-> m[k*vlen+j+1][i]))), 
    FData(Dat2d(TVect(TDouble, vlen), Length(mat), Length(mat[1])).setValue(
    Value(TArray(TArray(TVect(TDouble, vlen), Length(mat[1])), Length(mat)), 
        List(mat, row->Value(TArray(TVect(TDouble, vlen), Length(row)), 
        List(row, vel->Value(TVect(TDouble, vlen), List(vel, k->V(k))))))))
    ));
_make3DFDataVec := (t, vlen) -> let(
    tensor := List([0..Length(t)/vlen-1], u->List([1..Length(t[1])], (k)->List([1..Length(t[1][1])], (i)->List([0..vlen-1], (j)-> 
        t[u*vlen+j+1][k][i])))), 
    FData(Dat3d(TVect(TDouble, vlen), Length(tensor), Length(tensor[1]), Length(tensor[1][1])).setValue(
    Value(TArray(TArray(TArray(TVect(TDouble, vlen), Length(tensor[1][1])), Length(tensor[1])), Length(tensor)),
        List(tensor, 
        mat->Value(TArray(TArray(TVect(TDouble, vlen), Length(mat)), Length(mat[1])), 
            List(mat, row->Value(TArray(TVect(TDouble, vlen), Length(row)), 
            List(row, vel->Value(TVect(TDouble, vlen), List(vel, k->V(k))))))))
    ))));

ImportAll(platforms.avx);

Include(spl);
Include(proof);
Include(sigmaspl);
Include(sumsgen);
Include(tspl);
Include(sums2code);
Include(breakdown);
Include(code);
Include(rewrite);
Include(codegen);
Include(funcgen);
Include(unparse);
Include(opts);
Include(ivarith);
Include(formal_compile);
Include(translate);
Include(arctan);

Include(state);

##
#F IncludeScript( <file name> )
##
##	Read and evaluate the script in the current namespace.
##
##	Returns true if successful, otherwise returns false.
##
IncludeScript := function(filename)
	local allImports, lastPackage, tryRet;
	
	allImports := CurrentImports();
	
	if Length(allImports) > 0 then
		lastPackage := Last(allImports);
		tryRet := Try(READ(filename, lastPackage));
	else
		tryRet := Try(Read(filename));
	fi;
	
	if IsList(tryRet) then
		return Last(tryRet);
	else
		return tryRet;
	fi;
end;

