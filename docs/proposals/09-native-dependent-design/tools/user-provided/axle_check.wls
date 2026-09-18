#!/usr/bin/env wolframscript
(* Check a Lean file with the AXLE remote Lean service from Wolfram Language.

   As a script:  axle_check.wls SOURCE.lean [ENVIRONMENT [AUDIT.lean [THEOREM]]]
     (AUDIT.lean is appended minus its import lines and must print the axioms
     of THEOREM; pass "" for AUDIT.lean to use a built-in `#print axioms THEOREM`.)
   Interactively:  Get["axle_check.wls"]; AxleCheck["File.lean", "lean-4.34.0", "checks/Axioms.lean"]

   * the body and the response travel as UTF-8 byte arrays
     (ExportByteArray / ImportByteArray), since string round-trips corrupt
     Lean's Unicode;
   * `okay` alone is not a verdict: failed_declarations, Lean errors,
     `sorry` warnings, the `#print axioms` line and the echoed content are
     all checked;
   * an unknown environment name comes back as HTTP 200 with "user_error".
   See README.md in this directory.
*)

ClearAll[AxleCheck];
Options[AxleCheck] = {"Endpoint" -> "https://axle.axiommath.ai/api/v1/check",
  "Theorem" -> Automatic, "TimeoutSeconds" -> 120, "IgnoreImports" -> False,
  "AllowedAxioms" -> {"propext", "Classical.choice", "Quot.sound"}};

AxleCheck[path_String, environment_String : "lean-4.34.0", auditPath_String : "",
   theoremArg : (_String | Automatic) : Automatic, OptionsPattern[]] := Module[
  {source, audit, content, body, response, result, lean, tool, infos, axioms, problems,
   sorries, theorem, receipt, out},
  theorem = If[theoremArg =!= Automatic, theoremArg, OptionValue["Theorem"]];
  source = FromCharacterCode[BinaryReadList[path, "Byte"], "UTF8"];
  If[auditPath =!= "" && FileExistsQ[auditPath],
    audit = StringJoin[Riffle[Select[StringSplit[
      FromCharacterCode[BinaryReadList[auditPath, "Byte"], "UTF8"], "\n"],
      ! StringStartsQ[#, "import "] &], "\n"]];
    If[theorem === Automatic,
      theorem = First[StringCases[audit, StartOfLine ~~ "#print axioms " ~~
        n : Except[WhitespaceCharacter] .. :> n], Automatic]],
    If[theorem === Automatic,
      Print["no audit file: give the theorem name as the fourth argument"];
      Return[$Failed]];
    audit = "#print axioms " <> theorem <> "\n#eval Lean.versionString\n"];
  If[theorem === Automatic,
    Print["the audit file prints no axioms: give the theorem name as the fourth argument"];
    Return[$Failed]];
  content = StringTrim[source, RegularExpression["\n+$"]] <> "\n\n" <> audit;
  body = ExportByteArray[<|"content" -> content, "environment" -> environment,
    "ignore_imports" -> OptionValue["IgnoreImports"], "theorems_only" -> False,
    "timeout_seconds" -> OptionValue["TimeoutSeconds"]|>, "RawJSON"];
  response = URLRead[HTTPRequest[OptionValue["Endpoint"], <|"Method" -> "POST",
    "Headers" -> {"Content-Type" -> "application/json; charset=utf-8"},
    "Body" -> body|>], TimeConstraint -> OptionValue["TimeoutSeconds"] + 90];
  If[response["StatusCode"] =!= 200,
    Print["HTTP ", response["StatusCode"], ": ", response["Body"]]; Return[$Failed]];
  result = ImportByteArray[response["BodyByteArray"], "RawJSON"];
  If[KeyExistsQ[result, "user_error"],
    Print["service rejected the request: ", result["user_error"]]; Return[$Failed]];
  lean = Lookup[result, "lean_messages", <||>];
  tool = Lookup[result, "tool_messages", <||>];
  infos = StringJoin[Riffle[Lookup[lean, "infos", {}], "\n"]];
  axioms = With[{m = StringCases[infos,
      "'" <> theorem <> "' depends on axioms: [" ~~ a : Except["]"] ... ~~ "]" :> a]},
    Which[m =!= {}, StringTrim /@ StringSplit[First[m], ","],
      StringContainsQ[infos, "'" <> theorem <> "' does not depend on any axioms"], {},
      True, None]];
  sorries = Select[Lookup[lean, "warnings", {}], StringContainsQ["declaration uses `sorry`"]];
  problems = Flatten[{
    If[! TrueQ[result["okay"]], "okay is not true", {}],
    If[Lookup[result, "failed_declarations", {"missing"}] =!= {},
      "failed declarations: " <> ToString[result["failed_declarations"]], {}],
    If[Lookup[lean, "errors", {}] =!= {}, "Lean errors", {}],
    If[Lookup[tool, "errors", {}] =!= {}, "service errors", {}],
    If[sorries =!= {}, "declarations use sorry", {}],
    If[axioms === None, "no #print axioms output for " <> theorem,
      If[Complement[axioms, OptionValue["AllowedAxioms"]] =!= {},
        "disallowed axioms: " <> ToString[axioms], {}]],
    If[! OptionValue["IgnoreImports"] && StringQ[result["content"]] &&
        StringTrim[result["content"]] =!= StringTrim[content],
      "the service processed different content than was sent", {}]}];
  receipt = <|"source" -> path,
    "source_sha256" -> Hash[ByteArray[ToCharacterCode[source, "UTF8"]], "SHA256", "HexString"],
    "environment" -> environment, "verdict" -> If[problems === {}, "PASS", "FAIL"],
    "problems" -> problems, "axioms" -> If[axioms === None, Null, axioms],
    "request_id" -> Lookup[Lookup[result, "info", <||>], "request_id"],
    "response" -> KeyDrop[result, {"content"}]|>;
  out = path <> ".axle.json";
  Export[out, receipt, "RawJSON"];
  Print[receipt["verdict"], ": ", path, " in ", environment, " (request ",
    receipt["request_id"], "); receipt ", out];
  Do[Print["problem: ", p], {p, problems}];
  Do[Print["service warning: ", w], {w, Lookup[tool, "warnings", {}]}];
  receipt];

(* Command-line entry point.  `wolframscript -file` fills $ScriptCommandLine;
   a bare kernel (`wolfram.exe -script FILE ARGS`) leaves it empty and keeps
   the arguments in $CommandLine after the script path, so both are read. *)
$ProgressReporting = False;
scriptArgs = If[Length[$ScriptCommandLine] >= 2, Rest[$ScriptCommandLine],
  With[{pos = FirstPosition[$CommandLine, "-script", {}]},
    If[pos === {}, {}, Drop[$CommandLine, First[pos] + 1]]]];
If[scriptArgs =!= {},
  With[{r = AxleCheck @@ scriptArgs},
    Exit[If[AssociationQ[r] && r["verdict"] === "PASS", 0, 1]]]];
