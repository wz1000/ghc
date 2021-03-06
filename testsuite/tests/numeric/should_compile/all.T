test('T7116', normal, run_command, ['$MAKE -s --no-print-directory T7116'])
# These test Core output that depends upon integer-gmp
test('T14170', reqlib("integer-gmp"), run_command, ['$MAKE -s --no-print-directory T14170'])
test('T14465', reqlib("integer-gmp"), run_command, ['$MAKE -s --no-print-directory T14465'])
test('T7895', normal, compile, [''])
test('T7881', normal, compile, [''])
# For T8542, the hpc way adds extra annotations that prevent
# the appropriate expression to be detected, after
# desugaring, so we don't get the warning we expect.
test('T8542', omit_ways(['hpc']), compile, [''])
test('T10929', normal, compile, [''])
