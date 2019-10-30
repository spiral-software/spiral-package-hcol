# spiral-package-hcol

This is the SPIRAL package for the **Hybrid Control Operator Language** (HCOL).

Installation
------------

Clone this repository into the namespaces/packages subdirectory of your SPIRAL installation tree and rename it to "hcol".  For example, from the namespaces/packages directory:

```
git clone https://github.com/spiral-software/spiral-package-hcol.git hcol
```


Sample script
-------------

This is a simple HCOL script to test your installation.  It generates a C function that sums three double precision numbers.  
For more involved scripts see [examples.md](./examples.md).

```
Load(hcol);
Import(hcol);

opts := HCOLopts.getOpts(rec());
opts.useCReturn := true;
opts.YType := TPtr(T_Real(64));

hcol := Reduction(3, (a, b)->add(a, b), V(0), False);

icode := CoSynthesize(hcol, opts);

PrintCode("sum", icode, opts);
```
