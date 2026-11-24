for seed in $(seq 101 120); do
    echo "===== seed=$seed ====="
    ./ag_frvote --m 3 --q 2 --a 2 --b 1 \
        --errors 5 --M 21 --len 29 \
        -bms2-check "$seed"
done