# Vancomycert proof artefacts
The proof can be reproduced by using [vehicle](https://github.com/vehicle-lang/vehicle) and [mathcomp analysis](https://github.com/math-comp/analysis) version 1.16.0.

To do so, use this command to build the file `Spec.v`, the Rocq extraction of `pk.vcl`. You can change the parameters `-p` in the compile command and the proof will still go through. A `_CoqProject` file has also been provided for ease of building.
```shell
vehicle compile itp \
  -t Rocq \
  -o Spec.v \
  -s pk.vcl \
  -p Ka:4.5 \
  -p Ke:3.5 \
  -p Vd:10 \
  -p C_safe:60 \
  -p ttd:2 \
  -p Ka_over:0.3228 \
  -p Ka_under:0.3227 \
  -p Ke_over:0.415 \
  -p Ke_under:0.4149 \
  -p eps:0.001 \
  -r
```
