# Coverage Report

Total executable lines: 9
Covered lines: 9
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def topKFrequent(nums, k):
2: ✓     freq = {}
3: ✓     first_index = {}
4: ✓     for i, num in enumerate(nums):
5: ✓         freq[num] = freq.get(num, 0) + 1
6: ✓         if num not in first_index:
7: ✓             first_index[num] = i
8: ✓     sorted_nums = sorted(freq.keys(), key=lambda x: (-freq[x], first_index[x]))
9: ✓     return sorted_nums[:k]
```

## Complete Test File

```python
def topKFrequent(nums, k):
    freq = {}
    first_index = {}
    for i, num in enumerate(nums):
        freq[num] = freq.get(num, 0) + 1
        if num not in first_index:
            first_index[num] = i
    sorted_nums = sorted(freq.keys(), key=lambda x: (-freq[x], first_index[x]))
    return sorted_nums[:k]

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = topKFrequent([1, 1, 1, 2, 2, 3], 2)
        assert result == [1, 2], f"Test 1 failed: got {result}, expected {[1, 2]}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = topKFrequent([4, 1, -1, 2, -1, 2, 3], 2)
        assert result == [-1, 2], f"Test 2 failed: got {result}, expected {[-1, 2]}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = topKFrequent([5], 1)
        assert result == [5], f"Test 3 failed: got {result}, expected {[5]}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = topKFrequent([7, 7, 7, 8, 8, 9], 1)
        assert result == [7], f"Test 4 failed: got {result}, expected {[7]}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = topKFrequent([], 0)
        assert result == [], f"Test 5 failed: got {result}, expected {[]}"
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
