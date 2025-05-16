# Coverage Report

Total executable lines: 2
Covered lines: 2
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def MultipleReturns(x, y):
2: ✓     return (x + y, x - y)
```

## Complete Test File

```python
def MultipleReturns(x, y):
    return (x + y, x - y)

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = MultipleReturns(3, 2)
        assert result == '(5, 1)', f"Test 1 failed: got {result}, expected {'(5, 1)'}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = MultipleReturns(-2, 3)
        assert result == '(1, -5)', f"Test 2 failed: got {result}, expected {'(1, -5)'}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = MultipleReturns(0, 0)
        assert result == '(0, 0)', f"Test 3 failed: got {result}, expected {'(0, 0)'}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = MultipleReturns(10, 5)
        assert result == '(15, 5)', f"Test 4 failed: got {result}, expected {'(15, 5)'}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = MultipleReturns(-5, -10)
        assert result == '(-15, 5)', f"Test 5 failed: got {result}, expected {'(-15, 5)'}"
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
