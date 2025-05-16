# Coverage Report

Total executable lines: 26
Covered lines: 26
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def shortestBeautifulSubstring(s, k):
2: ✓     n = len(s)
3: ✓     p = [0] * (n + 1)
4: ✓     for i in range(n):
5: ✓         p[i+1] = p[i] + (1 if s[i] == '1' else 0)
6: ✓     indices = {}
7: ✓     for i, val in enumerate(p):
8: ✓         if val not in indices:
9: ✓             indices[val] = []
10: ✓         indices[val].append(i)
11: ✓     from bisect import bisect_right
12: ✓     best = None
13: ✓     best_len = float('inf')
14: ✓     for i in range(n):
15: ✓         req = p[i] + k
16: ✓         if req in indices:
17: ✓             lst = indices[req]
18: ✓             pos = bisect_right(lst, i)
19: ✓             if pos < len(lst):
20: ✓                 j = lst[pos]
21: ✓                 candidate = s[i:j]
22: ✓                 cand_len = j - i
23: ✓                 if cand_len < best_len or (cand_len == best_len and candidate < best):
24: ✓                     best = candidate
25: ✓                     best_len = cand_len
26: ✓     return best if best is not None else ""
```

## Complete Test File

```python
def shortestBeautifulSubstring(s, k):
    n = len(s)
    p = [0] * (n + 1)
    for i in range(n):
        p[i+1] = p[i] + (1 if s[i] == '1' else 0)
    indices = {}
    for i, val in enumerate(p):
        if val not in indices:
            indices[val] = []
        indices[val].append(i)
    from bisect import bisect_right
    best = None
    best_len = float('inf')
    for i in range(n):
        req = p[i] + k
        if req in indices:
            lst = indices[req]
            pos = bisect_right(lst, i)
            if pos < len(lst):
                j = lst[pos]
                candidate = s[i:j]
                cand_len = j - i
                if cand_len < best_len or (cand_len == best_len and candidate < best):
                    best = candidate
                    best_len = cand_len
    return best if best is not None else ""

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = shortestBeautifulSubstring('100011001', 3)
        assert result == '11001', f"Test 1 failed: got {result}, expected {'11001'}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = shortestBeautifulSubstring('1011', 2)
        assert result == '11', f"Test 2 failed: got {result}, expected {'11'}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = shortestBeautifulSubstring('000', 1)
        assert result == '', f"Test 3 failed: got {result}, expected {''}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = shortestBeautifulSubstring('11111', 3)
        assert result == '111', f"Test 4 failed: got {result}, expected {'111'}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = shortestBeautifulSubstring('10100101', 2)
        assert result == '101', f"Test 5 failed: got {result}, expected {'101'}"
        print(f"Test 5 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 5 failed: {e}")
        test_results.append(False)

    # Test case 6
    try:
        result = shortestBeautifulSubstring('1001001', 2)
        assert result == '1001', f"Test 6 failed: got {result}, expected {'1001'}"
        print(f"Test 6 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 6 failed: {e}")
        test_results.append(False)

    # Test case 7
    try:
        result = shortestBeautifulSubstring('10010001', 1)
        assert result == '1', f"Test 7 failed: got {result}, expected {'1'}"
        print(f"Test 7 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 7 failed: {e}")
        test_results.append(False)

    # Test case 8
    try:
        result = shortestBeautifulSubstring('1001', 0)
        assert result == '0', f"Test 8 failed: got {result}, expected {'0'}"
        print(f"Test 8 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 8 failed: {e}")
        test_results.append(False)

    return test_results

if __name__ == '__main__':
    results = run_tests()
    print(f"\n{sum(results)}/{len(results)} tests passed")

```
