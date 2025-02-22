let currentSrc = ref ""
let currentModule = ref ""
let currentModuleName = ref ("" |> Name.create)
let runConfig = RunConfig.runConfig

(* Location printer: `filename:line: ' *)
let posToString (pos : Lexing.position) =
  let file = pos.Lexing.pos_fname in
  let line = pos.Lexing.pos_lnum in
  let col = pos.Lexing.pos_cnum - pos.Lexing.pos_bol in
  (file |> Filename.basename)
  ^ ":" ^ string_of_int line ^ ":" ^ string_of_int col

module Cli = struct
  let debug = ref false
  let ci = ref false

  (** The command was a -cmt variant (e.g. -exception-cmt) *)
  let cmtCommand = ref false

  let experimental = ref false
  let json = ref false
  let write = ref false
  let exitCode = ref false

  (* names to be considered live values *)
  let liveNames = ref ([] : string list)

  (* paths of files where all values are considered live *)

  let livePaths = ref ([] : string list)

  (* paths of files to exclude from analysis *)
  let excludePaths = ref ([] : string list)

  (* path of build-generated files for native projects *)
  let nativeBuildTarget = ref (None : string option)
end

module StringSet = Set.Make (String)

module LocSet = Set.Make (struct
  include CL.Location

  let compare = compare
end)

module FileSet = Set.Make (String)

module FileHash = struct
  include Hashtbl.Make (struct
    type t = string

    let hash (x : t) = Hashtbl.hash x
    let equal (x : t) y = x = y
  end)
end

module FileReferences = struct
  (* references across files *)
  let table = (FileHash.create 256 : FileSet.t FileHash.t)

  let findSet table key =
    try FileHash.find table key with Not_found -> FileSet.empty

  let add (locFrom : CL.Location.t) (locTo : CL.Location.t) =
    let key = locFrom.loc_start.pos_fname in
    let set = findSet table key in
    FileHash.replace table key (FileSet.add locTo.loc_start.pos_fname set)

  let addFile fileName =
    let set = findSet table fileName in
    FileHash.replace table fileName set

  let exists fileName = FileHash.mem table fileName

  let find fileName =
    match FileHash.find_opt table fileName with
    | Some set -> set
    | None -> FileSet.empty

  let iter f = FileHash.iter f table
end
