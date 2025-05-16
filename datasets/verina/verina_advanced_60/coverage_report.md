# Coverage Report

Total executable lines: 4
Covered lines: 4
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def partitionEvensOdds(nums):
2: ✓     evens = [x for x in nums if x % 2 == 0]
3: ✓     odds = [x for x in nums if x % 2 == 1]
4: ✓     return (evens, odds)
```

## Complete Test File

```python
def partitionEvensOdds(nums):
    evens = [x for x in nums if x % 2 == 0]
    odds = [x for x in nums if x % 2 == 1]
    return (evens, odds)

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = partitionEvensOdds([1, 2, 3, 4, 5, 6])
        assert result == '([2, 4, 6], [1, 3, 5])', f"Test 1 failed: got {result}, expected {'([2, 4, 6], [1, 3, 5])'}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = partitionEvensOdds([0, 7, 8, 9, 10])
        assert result == '([0, 8, 10], [7, 9])', f"Test 2 failed: got {result}, expected {'([0, 8, 10], [7, 9])'}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = partitionEvensOdds([])
        assert result == '([], [])', f"Test 3 failed: got {result}, expected {'([], [])'}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = partitionEvensOdds([2, 4, 6, 8])
        assert result == '([2, 4, 6, 8], [])', f"Test 4 failed: got {result}, expected {'([2, 4, 6, 8], [])'}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = partitionEvensOdds([1, 3, 5, 7])
        assert result == '([], [1, 3, 5, 7])', f"Test 5 failed: got {result}, expected {'([], [1, 3, 5, 7])'}"
        print(f"Test 5 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 5 failed: {e}")
        test_results.append(False)

    return test_results

if __name__ == '__main__':
    results = run_tests()
    print(f"\n{sum(results)}/{len(results)} tests passed")

```
