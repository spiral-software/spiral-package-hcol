# HCOL Examples

## Vector Length

### sqrt(X[1]^2 + X[2]^2 + X[3]^2 + X[4]^2)

```
Load(hcol);
Import(hcol);

opts := HCOLopts.getOpts(rec());
opts.useCReturn := true;
opts.YType := TPtr(T_Real(64));

len := 4;

funcname := "veclen4";
filename := "veclen4.c";

x := var("x", T_Real(64));
i := Ind(1);

hcol :=  OLCompose(
    PointWise(1, Lambda([x, i], sqrt(x))),
    Reduction(len, (a, b)->add(a, b), V(0), False),
    PointWise(len, Lambda([x, i], mul(x, x)))
);

icode := CoSynthesize(hcol, opts);

PrintTo(filename, "#define VECLEN " :: String(len) :: "\n");
AppendTo(filename, PrintCode(funcname, icode, opts));
```


## Multiple Inputs

### sin(x) + cos(y) + tan(x)


```
Load(hcol);
Import(hcol);

opts := HCOLopts.getOpts(rec());
opts.useCReturn := false;
opts.includes := ["<math.h>"];
opts.XType := TPtr(TInt);
X.t := TPtr(TInt);
opts.globalUnrolling := 2;
opts.YType := TPtr(TDouble);
opts.arrayDataModifier := "";
opts.arrayBufModifier := "";
funcname := "function_multi_input";
filename := "function_multi_input.c";
tx := var("tx", TInt);
ty := var("ty", TInt);
i := var("i", TInt);
n := var("N", TInt);
runs := Ind(n);
opts.params := [n];
__NUM_VAR__ := 2;

<#
sin(x) + cos(y) + tan(x)
#>

hcol := IterDirectSum(runs, n,
  OLCompose(
    BinOp(1, Lambda([tx,ty], add(tx,ty))),
    VStack(
      OLCompose(
        BinOp(1, Lambda([tx,ty], add(tx,ty))),
        VStack(
          OLCompose(
            PointWise(1, Lambda([tx,i], sin(tx))),
            GathH(__NUM_VAR__, 1, 0, 1)
          ),
          OLCompose(
            PointWise(1, Lambda([tx,i], cos(tx))),
            GathH(__NUM_VAR__, 1, 1, 1)
          )
        )
      ),
      OLCompose(
        PointWise(1, Lambda([tx,i], tan(tx))),
        GathH(__NUM_VAR__, 1, 0, 1)
      )
    )
  )
);

icode := CoSynthesize(hcol, opts);
PrintTo(filename, PrintCode(funcname, icode, opts));
```

## Conditional Inside Loop

### for i in 1::n do Y[i] = ((1.0) if (X[i] < 0) else (sin(X[i])))

```
Load(hcol);
Import(hcol);

opts := HCOLopts.getOpts(rec());
opts.useCReturn := false;
opts.includes := ["<math.h>"];
opts.XType := TPtr(TInt);
X.t := TPtr(TInt);
opts.globalUnrolling := 2;
opts.YType := TPtr(TDouble);
opts.arrayDataModifier := "";
opts.arrayBufModifier := "";
funcname := "F_003";
filename := "F_003.c";
tx := var("tx", TInt);
ty := var("ty", TInt);
i := var("i", TInt);
n := var("N", TInt);
runs := Ind(n);
opts.params := [n];
__NUM_VAR__ := 1;

<#
((1.0) if (x < 0) else (sin(x)))
#>

hcol := IterDirectSum(runs, n,
  TCond(
    TLess(
      GathH(__NUM_VAR__, 1, 0, 1),
      OLCompose(PointWise(1, Lambda([tx,i], 0)), GathH(__NUM_VAR__, 1, 0, 1))
    ),
    OLCompose(PointWise(1, Lambda([tx,i], 1.0)), GathH(__NUM_VAR__, 1, 0, 1)),
    OLCompose(
      PointWise(1, Lambda([tx,i], sin(tx))),
      GathH(__NUM_VAR__, 1, 0, 1)
    )
  )
);

icode := CoSynthesize(hcol, opts);
PrintTo(filename, PrintCode(funcname, icode, opts));
```

