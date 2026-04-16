-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def maxSubarraySumDivisibleByK_precond (arr : Array Int) (k : Int) : Prop :=
  -- !benchmark @start precond
  k > 0
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def maxSubarraySumDivisibleByK (arr : Array Int) (k : Int) : Int :=
  -- !benchmark @start code
  let n := arr.size
  if n = 0 || k = 0 then 0
  else
    --compute prefix sums for efficient subarray sum calculation
    let prefixSums := Id.run do
      let mut prefixSums := Array.mkArray (n + 1) 0
      for i in [0:n] do
        prefixSums := prefixSums.set! (i+1) (prefixSums[i]! + arr[i]!)
      prefixSums

    let result := Id.run do
      let mut best : Option Int := none
      for len in List.range (n+1) do
        if len % k = 0 && len > 0 then
          for start in [0:(n - len + 1)] do
            let endIdx := start + len
            let subarraySum := prefixSums[endIdx]! - prefixSums[start]!
            best := match best with
              | none => some subarraySum
              | some b => some (max b subarraySum)
      best

    match result with
    | none => 0
    | some s => s
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def maxSubarraySumDivisibleByK_postcond (arr : Array Int) (k : Int) (result: Int) : Prop :=
  -- !benchmark @start postcond
  let subarrays := List.range (arr.size) |>.flatMap (fun start =>
    List.range (arr.size - start + 1) |>.map (fun len => arr.extract start (start + len)))
  let divisibleSubarrays := subarrays.filter (fun subarray => subarray.size % k.toNat = 0 && subarray.size > 0)
  let subarraySums := divisibleSubarrays.map (fun subarray => subarray.toList.sum)
  -- No valid subarrays -> result is 0
  (subarraySums.length = 0 → result = 0) ∧
  -- Valid subarrays exist -> result is the maximum sum
  (subarraySums.length > 0 → result ∈ subarraySums ∧ subarraySums.all (fun sum => sum ≤ result))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem maxSubarraySumDivisibleByK_spec_satisfied (arr: Array Int) (k: Int) :
    maxSubarraySumDivisibleByK_postcond (arr) (k) (maxSubarraySumDivisibleByK (arr) (k)) := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
