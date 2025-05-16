# Coverage Report

Total executable lines: 4
Covered lines: 4
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def sumAndAverage(n):
2: ✓     total = n * (n + 1) // 2
3: ✓     average = total / n
4: ✓     return total, average
```

## Complete Test File

```python
def sumAndAverage(n):
    total = n * (n + 1) // 2
    average = total / n
    return total, average

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = sumAndAverage(5)
        assert result == '(15, 3.0)', f"Test 1 failed: got {result}, expected {'(15, 3.0)'}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = sumAndAverage(1)
        assert result == '(1, 1.0)', f"Test 2 failed: got {result}, expected {'(1, 1.0)'}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = sumAndAverage(10)
        assert result == '(55, 5.5)', f"Test 3 failed: got {result}, expected {'(55, 5.5)'}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = sumAndAverage(0)
        assert result == '(0, 0.0)', f"Test 4 failed: got {result}, expected {'(0, 0.0)'}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = sumAndAverage(2)
        assert result == '(3, 1.5)', f"Test 5 failed: got {result}, expected {'(3, 1.5)'}"
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
