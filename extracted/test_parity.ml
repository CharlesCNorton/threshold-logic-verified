(* Test driver for verified parity network *)

open Parity_verified

let () =
  Printf.printf "=== Verified Parity Network Test Suite ===\n\n";

  (* Test 1: Exhaustive verification *)
  Printf.printf "Test 1: Exhaustive verification (all 256 inputs)... ";
  if test_all then
    Printf.printf "PASSED\n"
  else
    Printf.printf "FAILED\n";

  (* Test 2: Specific test cases *)
  Printf.printf "\nTest 2: Specific test cases:\n";
  let test_cases = [
    ([false; false; false; false; false; false; false; false], false, "00000000");
    ([true; false; false; false; false; false; false; false], true,  "10000000");
    ([true; true; false; false; false; false; false; false], false, "11000000");
    ([true; true; true; false; false; false; false; false], true,  "11100000");
    ([true; true; true; true; true; true; true; true], false, "11111111");
    ([true; false; true; false; true; false; true; false], false, "10101010");
    ([false; true; false; true; false; true; false; true], false, "01010101");
    ([true; true; true; true; false; false; false; false], false, "11110000");
    ([true; false; false; false; false; false; false; true], false, "10000001");
    ([true; true; true; false; false; false; false; true], false, "11100001");
  ] in

  let passed = ref 0 in
  let failed = ref 0 in

  List.iter (fun (input, expected, name) ->
    let result = verified_parity input in
    let reference = reference_parity input in
    let hw = hamming_weight input in
    if result = expected && result = reference then begin
      Printf.printf "  %s (HW=%d): parity=%b ... OK\n" name hw result;
      incr passed
    end else begin
      Printf.printf "  %s (HW=%d): expected=%b, got=%b, ref=%b ... FAIL\n"
        name hw expected result reference;
      incr failed
    end
  ) test_cases;

  Printf.printf "\n  Passed: %d/%d\n" !passed (!passed + !failed);

  (* Test 3: Count by Hamming weight class *)
  Printf.printf "\nTest 3: Verification by Hamming weight class:\n";
  let hw_counts = Array.make 9 (0, 0) in (* (total, correct) *)

  List.iter (fun xs ->
    let hw = hamming_weight xs in
    let v = verified_parity xs in
    let r = reference_parity xs in
    let (total, correct) = hw_counts.(hw) in
    hw_counts.(hw) <- (total + 1, if v = r then correct + 1 else correct)
  ) all_8bit_inputs;

  for hw = 0 to 8 do
    let (total, correct) = hw_counts.(hw) in
    let expected_parity = if hw mod 2 = 1 then "odd" else "even" in
    Printf.printf "  HW=%d: %d/%d correct (expected %s parity)\n"
      hw correct total expected_parity
  done;

  (* Test 4: Performance *)
  Printf.printf "\nTest 4: Performance (1000 full verifications):\n";
  let t0 = Sys.time () in
  for _ = 1 to 1000 do
    let _ = List.map verified_parity all_8bit_inputs in ()
  done;
  let t1 = Sys.time () in
  Printf.printf "  256,000 evaluations in %.3f seconds\n" (t1 -. t0);
  Printf.printf "  %.0f evaluations/second\n" (256000.0 /. (t1 -. t0));

  (* Final summary *)
  Printf.printf "\n=== Summary ===\n";
  if test_all then
    Printf.printf "All tests PASSED. Verified parity network is correct.\n"
  else
    Printf.printf "Some tests FAILED.\n"
