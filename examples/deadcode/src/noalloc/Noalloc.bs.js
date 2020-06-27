// Generated by BUCKLESCRIPT, PLEASE EDIT WITH CARE


function foo(x, y) {
  return x + y | 0;
}

function bar(x) {
  return (x + x | 0) + 1 | 0;
}

function pair(x, y) {
  return [
          x,
          y
        ];
}

function unpair(param) {
  return param[0] + param[1] | 0;
}

function mixed(param, param$1) {
  var match = param$1[1];
  var match$1 = match[2];
  return [
          (param[0] + param[1] | 0) + param[2] | 0,
          (((((param$1[0] + match[0] | 0) + match[1] | 0) + match$1[0] | 0) + match$1[1] | 0) + match$1[2] | 0) + param$1[2] | 0
        ];
}

function duplicate(x) {
  return [
          x,
          x
        ];
}

function local(n) {
  return 34 + n | 0;
}

function quad(x) {
  var a_1 = x + 1 | 0;
  var a = [
    x,
    a_1
  ];
  return [
          a,
          a
        ];
}

function unpair2(v) {
  return v[0] + v[1] | 0;
}

function sumVec(v) {
  var match = v[1];
  var match$1 = v[0];
  return [
          match$1[0] + match[0] | 0,
          match$1[1] + match[1] | 0
        ];
}

function scale(s) {
  return [
          [
            s,
            1.0,
            1.0
          ],
          [
            1.0,
            s,
            1.0
          ],
          [
            1.0,
            1.0,
            s
          ]
        ];
}

function rotation(a) {
  return [
          [
            0.0,
            -1.0 * a,
            0.0
          ],
          [
            a,
            0.0,
            0.0
          ],
          [
            0.0,
            0.0,
            a
          ]
        ];
}

function mulVecVec(v1, v2) {
  var x = v1[0] * v2[0];
  var y = v1[1] * v2[1];
  var z = v1[2] * v2[2];
  return x + y + z;
}

function mulMatVec(m, v) {
  var x = mulVecVec(m[0], v);
  var y = mulVecVec(m[1], v);
  var z = mulVecVec(m[2], v);
  return [
          x,
          y,
          z
        ];
}

function restMatrix(v) {
  return mulMatVec(rotation(0.123), mulMatVec(scale(2.0), v));
}

function id(x) {
  return x;
}

function id2(x) {
  return x;
}

function retGlobal(param) {
  return 35;
}

var x = 34;

var fl = 2;

var y = 34;

var globalTuple = [
  1,
  2,
  3
];

export {
  x ,
  foo ,
  bar ,
  pair ,
  unpair ,
  mixed ,
  duplicate ,
  local ,
  quad ,
  fl ,
  unpair2 ,
  sumVec ,
  scale ,
  rotation ,
  mulVecVec ,
  mulMatVec ,
  restMatrix ,
  id ,
  id2 ,
  y ,
  retGlobal ,
  globalTuple ,
  
}
/* No side effect */
