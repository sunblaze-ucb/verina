# Coverage Report

Total executable lines: 9
Covered lines: 9
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def below_zero(operations):
2: ✓     cumulative = [0]
3: ✓     negative_found = False
4: ✓     for op in operations:
5: ✓         new_sum = cumulative[-1] + op
6: ✓         cumulative.append(new_sum)
7: ✓         if new_sum < 0:
8: ✓             negative_found = True
9: ✓     return cumulative, negative_found
```

## Complete Test File

```python
def below_zero(operations):
    cumulative = [0]
    negative_found = False
    for op in operations:
        new_sum = cumulative[-1] + op
        cumulative.append(new_sum)
        if new_sum < 0:
            negative_found = True
    return cumulative, negative_found

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = below_zero([1, 2, 3])
        assert result == '(#[0, 1, 3, 6], false)', f"Test 1 failed: got {result}, expected {'(#[0, 1, 3, 6], false)'}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = below_zero([-1, 2, -1])
        assert result == '(#[0, -1, 1, 0], true)', f"Test 2 failed: got {result}, expected {'(#[0, -1, 1, 0], true)'}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = below_zero([])
        assert result == '(#[0], false)', f"Test 3 failed: got {result}, expected {'(#[0], false)'}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = below_zero([0, 0, 0])
        assert result == '(#[0, 0, 0, 0], false)', f"Test 4 failed: got {result}, expected {'(#[0, 0, 0, 0], false)'}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = below_zero([10, -20, 5])
        assert result == '(#[0, 10, -10, -5], true)', f"Test 5 failed: got {result}, expected {'(#[0, 10, -10, -5], true)'}"
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
