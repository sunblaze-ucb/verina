# Coverage Report

Total executable lines: 10
Covered lines: 10
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def LinearSearch3(a, P):
2: ✓     if isinstance(P, str):
3: ✓         # Convert the string "fun x => condition" to a lambda function.
4: ✓         # Remove the "fun " prefix and split by "=>".
5: ✓         _, rest = P.split("fun", 1)
6: ✓         identifier, expr = rest.split("=>", 1)
7: ✓         identifier = identifier.strip()
8: ✓         expr = expr.strip()
9: ✓         P = eval("lambda {}: {}".format(identifier, expr))
10: ✓     for i, value in enumerate(a):
11: ✓         if P(value):
12: ✓             return i
```

## Complete Test File

```python
def LinearSearch3(a, P):
    if isinstance(P, str):
        # Convert the string "fun x => condition" to a lambda function.
        # Remove the "fun " prefix and split by "=>".
        _, rest = P.split("fun", 1)
        identifier, expr = rest.split("=>", 1)
        identifier = identifier.strip()
        expr = expr.strip()
        P = eval("lambda {}: {}".format(identifier, expr))
    for i, value in enumerate(a):
        if P(value):
            return i

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = LinearSearch3([4, 7, 2, 9], 'fun x => x > 5')
        assert result == 1, f"Test 1 failed: got {result}, expected {1}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = LinearSearch3([10, 8, 6, 4, 2], 'fun x => x < 5')
        assert result == 3, f"Test 2 failed: got {result}, expected {3}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = LinearSearch3([5, 3, 1, 2], 'fun x => x == 1')
        assert result == 2, f"Test 3 failed: got {result}, expected {2}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = LinearSearch3([0, 1, 2, 3], 'fun x => x == 0')
        assert result == 0, f"Test 4 failed: got {result}, expected {0}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = LinearSearch3([9, 9, 9, 9], 'fun x => x == 9')
        assert result == 0, f"Test 5 failed: got {result}, expected {0}"
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
