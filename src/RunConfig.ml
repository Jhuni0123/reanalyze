type t = {
  mutable bsbProjectRoot : string;
  mutable dva : bool;
  mutable projectRoot : string;
  mutable suppress : string list;
  mutable unsuppress : string list;
}

let runConfig =
  {
    bsbProjectRoot = "";
    dva = false;
    projectRoot = "";
    suppress = [];
    unsuppress = [];
  }

let all () =
  runConfig.dva <- true

let dva () = runConfig.dva <- true
