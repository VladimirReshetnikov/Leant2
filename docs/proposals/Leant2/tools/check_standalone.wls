(* Optional runner; invoked from the package root. The actual remote experiment
   used this HTTP/UTF-8 approach. The Python runner provides stricter validation. *)
source = FromCharacterCode[BinaryReadList["lean/Validation.lean"], "UTF8"];
request = <|"content" -> source, "environment" -> "lean-4.34.0",
  "ignore_imports" -> False, "theorems_only" -> False, "timeout_seconds" -> 120|>;
response = URLRead[HTTPRequest["https://axle.axiommath.ai/api/v1/check",
  <|"Method" -> "POST", "Headers" -> <|"Content-Type" -> "application/json"|>,
    "Body" -> ExportByteArray[request, "RawJSON"]|>]];
result = ImportByteArray[response["BodyByteArray"], "RawJSON"];
receipt = <|"source_sha256" -> Hash[source, "SHA256", "HexString"],
  "source_echo_matches" -> MemberQ[{source, source <> "\n"}, Lookup[result, "content", None]],
  "response" -> result|>;
Export["receipts/standalone-rerun.json", receipt, "RawJSON"];
Print[receipt];
