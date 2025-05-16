# Coverage Report

Total executable lines: 9
Covered lines: 9
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def findExponents(n, primes):
2: ✓     result = []
3: ✓     for p in primes:
4: ✓         exponent = 0
5: ✓         while n % p == 0:
6: ✓             n //= p
7: ✓             exponent += 1
8: ✓         result.append((p, exponent))
9: ✓     return result
```

## Complete Test File

```python
def findExponents(n, primes):
    result = []
    for p in primes:
        exponent = 0
        while n % p == 0:
            n //= p
            exponent += 1
        result.append((p, exponent))
    return result

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = findExponents(6, [2, 3])
        assert result == [(2, 1), (3, 1)], f"Test 1 failed: got {result}, expected {[(2, 1), (3, 1)]}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = findExponents(6285195213566005335561053533150026217291776, [2, 3, 5])
        assert result == [(2, 55), (3, 55), (5, 0)], f"Test 2 failed: got {result}, expected {[(2, 55), (3, 55), (5, 0)]}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = findExponents(360, [2, 3, 5])
        assert result == [(2, 3), (3, 2), (5, 1)], f"Test 3 failed: got {result}, expected {[(2, 3), (3, 2), (5, 1)]}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = findExponents(18903812908, [2, 43, 823, 133543])
        assert result == [(2, 2), (43, 1), (823, 1), (133543, 1)], f"Test 4 failed: got {result}, expected {[(2, 2), (43, 1), (823, 1), (133543, 1)]}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = findExponents(114514, [2, 31, 1847])
        assert result == [(2, 1), (31, 1), (1847, 1)], f"Test 5 failed: got {result}, expected {[(2, 1), (31, 1), (1847, 1)]}"
        print(f"Test 5 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 5 failed: {e}")
        test_results.append(False)

    # Test case 6
    try:
        result = findExponents(20241147794175, [3, 5, 7, 11, 31, 47])
        assert result == [(3, 3), (5, 2), (7, 1), (11, 3), (31, 1), (47, 3)], f"Test 6 failed: got {result}, expected {[(3, 3), (5, 2), (7, 1), (11, 3), (31, 1), (47, 3)]}"
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
