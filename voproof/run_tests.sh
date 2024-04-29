#!/bin/bash

prefix="cargo test --release --features print-trace"
postfix="-- --nocapture"

# for scale in 1000 2000 4000 8000 16000 32000 64000 128000; do # 256000 512000 1024000; do
  # echo "VOR1CS $scale" | tee -a test_result.txt
  # $prefix test_simple_r1cs_large_scale_$scale $postfix | egrep '^End:' | tee -a test_result.txt
  # echo "VOR1CS Prover Efficient $scale" | tee -a test_result.txt
  # $prefix test_simple_r1cs_pe_large_scale_$scale $postfix | egrep '^End:' | tee -a test_result.txt
  # echo "Marlin $scale" | tee -a test_result.txt
  # $prefix test_marlin_test_circuit_scale_$scale $postfix | egrep '^End:' | tee -a test_result.txt
# done

# for scale in 8 16 32 64; do # 256000 512000 1024000; do
  # echo "VOR1CS $scale" | tee -a test_result_mt.txt
  # $prefix test_r1cs_mt_$scale $postfix | egrep '^End:' | tee -a test_result_mt.txt
  # echo "VOR1CS Prover Efficient $scale" | tee -a test_result_mt.txt
  # $prefix test_r1cs_pe_mt_$scale $postfix | egrep '^End:' | tee -a test_result_mt.txt
  # echo "Marlin $scale" | tee -a test_result_mt.txt
  # $prefix test_marlin_mt_circuit_scale_$scale $postfix | egrep '^End:' | tee -a test_result_mt.txt
# done

# for scale in 8 16 32 64; do
  # echo "VOPLONK $scale" | tee -a test_result_mt.txt
  # $prefix test_pov_mt_$scale $postfix | egrep '^End:' | tee -a test_result_mt.txt
  # echo "VOPLONK Prover Efficient $scale" | tee -a test_result_mt.txt
  # $prefix test_pov_pe_mt_$scale $postfix | egrep '^End:' | tee -a test_result_mt.txt
# done

# for scale in 8 16 32 64; do
  # echo "Groth16 $scale" | tee -a test_result_mt.txt
  # $prefix test_groth16_mt_circuit_scale_$scale $postfix | egrep '^End:' | tee -a test_result_mt.txt
# done

for scale in 8 16 32 64; do
  echo "PLONK $scale" | tee -a test_result_mt.txt
  $prefix test_plonk_mt_$scale $postfix | egrep '^End:' | tee -a test_result_mt.txt
done
