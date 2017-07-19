/*
 * Name: Property argument expression
 * Description:  Test that you can use arbitrary expressions in property
 * applications
 * Expected: Accept
 * Model: relaxed.c
 */

property test(int a) : 1 == 1;
property_r test_r(int a) : 1 == 1;

assert(test(1));
assert(test(1+2));
assert(test_r(1));
assert(test_r(1+2));
