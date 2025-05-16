# Coverage Report

Total executable lines: 7
Covered lines: 7
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def double_array_elements(s):
2: ✓     def helper(index):
3: ✓         if index < len(s):
4: ✓             s[index] *= 2
5: ✓             helper(index + 1)
6: ✓     helper(0)
7: ✓     return s
```

## Complete Test File

```python
def double_array_elements(s):
    def helper(index):
        if index < len(s):
            s[index] *= 2
            helper(index + 1)
    helper(0)
    return s

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = double_array_elements([])
        assert result == [], f"Test 1 failed: got {result}, expected {[]}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = double_array_elements([1, 2, 3, 4, 5])
        assert result == [2, 4, 6, 8, 10], f"Test 2 failed: got {result}, expected {[2, 4, 6, 8, 10]}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = double_array_elements([0, -1, 5])
        assert result == [0, -2, 10], f"Test 3 failed: got {result}, expected {[0, -2, 10]}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = double_array_elements([100])
        assert result == [200], f"Test 4 failed: got {result}, expected {[200]}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = double_array_elements([-3, -4])
        assert result == [-6, -8], f"Test 5 failed: got {result}, expected {[-6, -8]}"
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
