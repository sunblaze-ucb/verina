# Coverage Report

Total executable lines: 2
Covered lines: 2
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def Swap(X, Y):
2: ✓     return (Y, X)
```

## Complete Test File

```python
def Swap(X, Y):
    return (Y, X)

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = Swap(1, 2)
        assert result == '(2, 1)', f"Test 1 failed: got {result}, expected {'(2, 1)'}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = Swap(0, 0)
        assert result == '(0, 0)', f"Test 2 failed: got {result}, expected {'(0, 0)'}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = Swap(-1, 5)
        assert result == '(5, -1)', f"Test 3 failed: got {result}, expected {'(5, -1)'}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = Swap(100, -100)
        assert result == '(-100, 100)', f"Test 4 failed: got {result}, expected {'(-100, 100)'}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = Swap(42, 42)
        assert result == '(42, 42)', f"Test 5 failed: got {result}, expected {'(42, 42)'}"
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
