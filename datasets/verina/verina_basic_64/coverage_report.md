# Coverage Report

Total executable lines: 2
Covered lines: 2
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def insert(oline, l, nl, p, atPos):
2: ✓     return oline[:atPos] + nl[:p] + oline[atPos:l]
```

## Complete Test File

```python
def insert(oline, l, nl, p, atPos):
    return oline[:atPos] + nl[:p] + oline[atPos:l]

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = insert(['a', 'b', 'c', 'd', 'e'], 5, ['X', 'Y'], 2, 2)
        assert result == ['a', 'b', 'X', 'Y', 'c', 'd', 'e'], f"Test 1 failed: got {result}, expected {['a', 'b', 'X', 'Y', 'c', 'd', 'e']}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = insert(['H', 'e', 'l', 'l', 'o'], 5, ['W', 'o', 'r', 'l', 'd'], 5, 0)
        assert result == ['W', 'o', 'r', 'l', 'd', 'H', 'e', 'l', 'l', 'o'], f"Test 2 failed: got {result}, expected {['W', 'o', 'r', 'l', 'd', 'H', 'e', 'l', 'l', 'o']}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = insert(['L', 'e', 'a', 'n'], 4, ['4'], 1, 4)
        assert result == ['L', 'e', 'a', 'n', '4'], f"Test 3 failed: got {result}, expected {['L', 'e', 'a', 'n', '4']}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = insert(['T', 'e', 's', 't'], 4, [], 0, 2)
        assert result == ['T', 'e', 's', 't'], f"Test 4 failed: got {result}, expected {['T', 'e', 's', 't']}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = insert(['1', '2', '3', '4', '5', '6'], 5, ['a', 'b', 'c'], 3, 3)
        assert result == ['1', '2', '3', 'a', 'b', 'c', '4', '5'], f"Test 5 failed: got {result}, expected {['1', '2', '3', 'a', 'b', 'c', '4', '5']}"
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
