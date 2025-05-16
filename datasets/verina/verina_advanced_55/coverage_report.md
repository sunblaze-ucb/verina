# Coverage Report

Total executable lines: 7
Covered lines: 7
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1:   from functools import reduce
2:   
3: ✓ def mostFrequent(xs):
4: ✓     freq = reduce(lambda acc, x: {**acc, x: acc.get(x, 0) + 1}, xs, {})
5: ✓     max_freq = max(freq.values())
6: ✓     for x in xs:
7: ✓         if freq[x] == max_freq:
8: ✓             return x
```

## Complete Test File

```python
from functools import reduce

def mostFrequent(xs):
    freq = reduce(lambda acc, x: {**acc, x: acc.get(x, 0) + 1}, xs, {})
    max_freq = max(freq.values())
    for x in xs:
        if freq[x] == max_freq:
            return x

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = mostFrequent([1, 2, 2, 3])
        assert result == 2, f"Test 1 failed: got {result}, expected {2}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = mostFrequent([4, 4, 5, 5, 4])
        assert result == 4, f"Test 2 failed: got {result}, expected {4}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = mostFrequent([9])
        assert result == 9, f"Test 3 failed: got {result}, expected {9}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = mostFrequent([1, 2, 3, 1, 2, 3, 2])
        assert result == 2, f"Test 4 failed: got {result}, expected {2}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = mostFrequent([7, 7, 8, 8, 9, 9, 7])
        assert result == 7, f"Test 5 failed: got {result}, expected {7}"
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
