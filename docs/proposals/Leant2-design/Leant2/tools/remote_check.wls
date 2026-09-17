(* Load with Get["tools/remote_check.wls"], then call
   AxleCheckSource[Import["prototype/MicroSynth.lean", "Text"]].
   The HTTP/UTF-8 request mechanism was used for the article experiments.
   This reusable wrapper's audit parsing is an additional convenience. *)
ClearAll[AxleCheckSource];
AxleCheckSource[source_String, environment_String : "lean-4.34.0",
    allowed_List : {"propext", "Quot.sound"}] := Module[
  {request, http, response, problems = {}, lean, service, expected,
   reports, matching, lines, extracted, names, audits = <||>},
  request = <|"content" -> source, "environment" -> environment,
    "ignore_imports" -> False, "theorems_only" -> False,
    "timeout_seconds" -> 90|>;
  http = URLRead[HTTPRequest["https://axle.axiommath.ai/api/v1/check", <|
    "Method" -> "POST", "Headers" -> <|"Content-Type" -> "application/json"|>,
    "Body" -> ExportByteArray[request, "RawJSON"]|>]];
  If[FailureQ[http], Return[<|"passed" -> False, "transportFailure" -> http|>]];
  response = Quiet[Check[ImportByteArray[http["BodyByteArray"], "RawJSON"], $Failed]];
  If[!AssociationQ[response], Return[<|"passed" -> False,
    "problems" -> {"Response is not a JSON object"}|>]];
  lean = Lookup[response, "lean_messages", <||>];
  service = Lookup[response, "tool_messages", <||>];
  If[http["StatusCode"] =!= 200, AppendTo[problems, "HTTP status is not 200"]];
  If[KeyExistsQ[response, "user_error"], AppendTo[problems, response["user_error"]]];
  If[Lookup[response, "okay", False] =!= True, AppendTo[problems, "okay is not true"]];
  If[Lookup[response, "failed_declarations", {}] =!= {},
    AppendTo[problems, "Failed declarations"]];
  If[Lookup[lean, "errors", {}] =!= {} || Lookup[service, "errors", {}] =!= {},
    AppendTo[problems, "Compiler or service errors"]];
  If[StringTrim[Lookup[response, "content", ""]] =!= StringTrim[source],
    AppendTo[problems, "Echoed source changed beyond surrounding whitespace"]];
  If[AnyTrue[Lookup[lean, "warnings", {}],
      StringContainsQ[#, RegularExpression["declaration uses.*sorry"]] &],
    AppendTo[problems, "A declaration uses sorry"]];
  expected = StringCases[source,
    RegularExpression["(?m)^\\s*#print\\s+axioms\\s+(\\S+)\\s*$"] -> "$1"];
  lines = Lookup[lean, "infos", {}];
  If[expected === {}, AppendTo[problems, "No axiom audit directives found"]];
  Do[
    matching = Select[lines, StringContainsQ[#, "'" <> name <> "'"] ||
      StringContainsQ[#, "." <> name <> "'"] &];
    If[Length[matching] =!= 1,
      AppendTo[problems, "Missing or ambiguous axiom report: " <> name],
      extracted = StringCases[First[matching],
        RegularExpression["depends on axioms: \\[([^\\]]*)\\]"] -> "$1"];
      names = If[extracted === {}, {},
        DeleteCases[StringTrim /@ StringSplit[First[extracted], ","], ""]];
      If[extracted === {} && !StringContainsQ[First[matching], "does not depend on any axioms"],
        AppendTo[problems, "Unrecognized axiom report: " <> name]];
      AssociateTo[audits, name -> names];
      If[Complement[names, allowed] =!= {} || MemberQ[names, "sorryAx"],
        AppendTo[problems, "Disallowed axioms: " <> name]]
    ], {name, expected}];
  <|"passed" -> (problems === {}), "problems" -> problems,
    "axiomReports" -> audits, "request" -> request, "response" -> response|>
];
