
# Copyright 2018-2019, Carnegie Mellon University
# See LICENSE for details

CoSynthesize := function(t, opts) 
    local tmp, f;
    tmp := Copy(t);
    for f in opts.csStrategy do
        tmp := f(tmp, opts);
    od;
    return tmp;
end;

ExportCode := function(c)
    local vars;
    vars := FoldL(Collect(c, var), (a,b)->When(not b.id in List(a, i->i.id), Concat([b],a), a), []);
    Print("let(", DoForAll(vars, i->Print(i.id, " := var(\"", i.id, "\", ", i.t, "),\n")), c, ")");
end;

ExportCProg := function(c, opts)
    Print(opts.doc::
        "\n");
    PrintCode(opts.subName, c, opts);
end;


ExportInclude := function(c, opts)
    local parameters, id, unparser, oopts, macro;
    
    unparser := Copy(opts.unparser);
    opts.unparser.opts:=opts;
    macro := "__"::StringToUpper(opts.filename)::"_H__";
    
    Print(opts.doc::
        "\n"::
        "#ifndef "::macro::"\n"::
        "#define "::macro::"\n\n"::
        "#ifdef __cplusplus\n"::
        "extern \"C\" {\n"::
        "#endif\n");
        
    parameters:=Flat(c.params);
    id := opts.subName;
    Print("\n", 
        When(IsBound(c.inline) and c.inline, "inline ",""),
        opts.funcModifier, opts.unparser.declare(c.ret, var(id, c.ret), 0, 1), "(",
            DoForAllButLast(parameters, p->Print(unparser.declare(p.t, p,0,1), ", ")),
            When(Length(parameters)>0, unparser.declare(Last(parameters).t, Last(parameters),0,1), ""), ");\n");
        
    Print("\n#ifdef __cplusplus\n"::
        "}\n"::
        "#endif\n\n"::    
        "#endif\n");
    opts.unparser := unparser;
end;

