# Coverage Report

Total executable lines: 17
Covered lines: 17
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def nthUglyNumber(n):
2: ✓     ugly = [0] * n
3: ✓     ugly[0] = 1
4: ✓     i2 = i3 = i5 = 0
5: ✓     for i in range(1, n):
6: ✓         next2 = ugly[i2] * 2
7: ✓         next3 = ugly[i3] * 3
8: ✓         next5 = ugly[i5] * 5
9: ✓         next_ugly = min(next2, next3, next5)
10: ✓         ugly[i] = next_ugly
11: ✓         if next_ugly == next2:
12: ✓             i2 += 1
13: ✓         if next_ugly == next3:
14: ✓             i3 += 1
15: ✓         if next_ugly == next5:
16: ✓             i5 += 1
17: ✓     return ugly[-1]
```

## Complete Test File

```python
def nthUglyNumber(n):
    ugly = [0] * n
    ugly[0] = 1
    i2 = i3 = i5 = 0
    for i in range(1, n):
        next2 = ugly[i2] * 2
        next3 = ugly[i3] * 3
        next5 = ugly[i5] * 5
        next_ugly = min(next2, next3, next5)
        ugly[i] = next_ugly
        if next_ugly == next2:
            i2 += 1
        if next_ugly == next3:
            i3 += 1
        if next_ugly == next5:
            i5 += 1
    return ugly[-1]

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = nthUglyNumber(1)
        assert result == 1, f"Test 1 failed: got {result}, expected {1}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = nthUglyNumber(10)
        assert result == 12, f"Test 2 failed: got {result}, expected {12}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = nthUglyNumber(15)
        assert result == 24, f"Test 3 failed: got {result}, expected {24}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = nthUglyNumber(5)
        assert result == 5, f"Test 4 failed: got {result}, expected {5}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = nthUglyNumber(7)
        assert result == 8, f"Test 5 failed: got {result}, expected {8}"
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
