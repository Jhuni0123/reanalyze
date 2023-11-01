(* Adapted from https://github.com/LexiFi/dead_code_analyzer *)

module Config = struct
  (* Turn on type analysis *)
  let analyzeTypes = ref true

  let analyzeExternals = ref false

  let reportUnderscore = false

  let reportTypesDeadOnlyInInterface = false

  let recursiveDebug = false

  let warnOnCircularDependencies = false
end
