# Coverage Report

Total executable lines: 15
Covered lines: 15
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def letterCombinations(digits):
2: ✓     if not digits:
3: ✓         return []
4: ✓     mapping = {
5: ✓         '2': "abc",
6: ✓         '3': "def",
7: ✓         '4': "ghi",
8: ✓         '5': "jkl",
9: ✓         '6': "mno",
10: ✓         '7': "pqrs",
11: ✓         '8': "tuv",
12: ✓         '9': "wxyz"
13: ✓     }
14: ✓     combinations = [""]
15: ✓     for digit in digits:
16: ✓         if digit not in mapping:
17: ✓             combinations = []
18: ✓             break
19: ✓         temp = []
20: ✓         for combination in combinations:
21: ✓             for letter in mapping[digit]:
22: ✓                 temp.append(combination + letter)
23: ✓         combinations = temp
24: ✓     return combinations
```

## Complete Test File

```python
def letterCombinations(digits):
    if not digits:
        return []
    mapping = {
        '2': "abc",
        '3': "def",
        '4': "ghi",
        '5': "jkl",
        '6': "mno",
        '7': "pqrs",
        '8': "tuv",
        '9': "wxyz"
    }
    combinations = [""]
    for digit in digits:
        if digit not in mapping:
            combinations = []
            break
        temp = []
        for combination in combinations:
            for letter in mapping[digit]:
                temp.append(combination + letter)
        combinations = temp
    return combinations

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = letterCombinations('')
        assert result == [], f"Test 1 failed: got {result}, expected {[]}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = letterCombinations('2')
        assert result == ['a', 'b', 'c'], f"Test 2 failed: got {result}, expected {['a', 'b', 'c']}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = letterCombinations('9')
        assert result == ['w', 'x', 'y', 'z'], f"Test 3 failed: got {result}, expected {['w', 'x', 'y', 'z']}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = letterCombinations('23')
        assert result == ['ad', 'ae', 'af', 'bd', 'be', 'bf', 'cd', 'ce', 'cf'], f"Test 4 failed: got {result}, expected {['ad', 'ae', 'af', 'bd', 'be', 'bf', 'cd', 'ce', 'cf']}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = letterCombinations('27')
        assert result == ['ap', 'aq', 'ar', 'as', 'bp', 'bq', 'br', 'bs', 'cp', 'cq', 'cr', 'cs'], f"Test 5 failed: got {result}, expected {['ap', 'aq', 'ar', 'as', 'bp', 'bq', 'br', 'bs', 'cp', 'cq', 'cr', 'cs']}"
        print(f"Test 5 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 5 failed: {e}")
        test_results.append(False)

    # Test case 6
    try:
        result = letterCombinations('0')
        assert result == [], f"Test 6 failed: got {result}, expected {[]}"
        print(f"Test 6 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 6 failed: {e}")
        test_results.append(False)

    return test_results

if __name__ == '__main__':
    results = run_tests()
    print(f"\n{sum(results)}/{len(results)} tests passed")

```
