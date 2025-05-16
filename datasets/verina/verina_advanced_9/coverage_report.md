# Coverage Report

Total executable lines: 7
Covered lines: 7
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def countSumDivisibleBy(n, d):
2: ✓     count = 0
3: ✓     for num in range(n):
4: ✓         s = sum(int(ch) for ch in str(num))
5: ✓         if s % d == 0:
6: ✓             count += 1
7: ✓     return count
```

## Complete Test File

```python
def countSumDivisibleBy(n, d):
    count = 0
    for num in range(n):
        s = sum(int(ch) for ch in str(num))
        if s % d == 0:
            count += 1
    return count

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = countSumDivisibleBy(0, 2)
        assert result == 0, f"Test 1 failed: got {result}, expected {0}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = countSumDivisibleBy(1, 2)
        assert result == 1, f"Test 2 failed: got {result}, expected {1}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = countSumDivisibleBy(10, 3)
        assert result == 4, f"Test 3 failed: got {result}, expected {4}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = countSumDivisibleBy(12, 2)
        assert result == 6, f"Test 4 failed: got {result}, expected {6}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = countSumDivisibleBy(20, 5)
        assert result == 4, f"Test 5 failed: got {result}, expected {4}"
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
