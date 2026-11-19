# BBGS binary AG/ECP decoder (single-file C)

## 概要

この版は BBGS の二元曲線族に絞った単一ファイル実装です。曲線固有部分は次の3か所にまとめています。

- `bbgs_define_equation(x,y)`: BBGS の定義式
- `bb_point_data(x,y,&z,&w)`: 補助関数 `u,z,w` の構成
- `bb_build_basis(...)`: Hu の Omega 格子に基づく基底生成

ECP 復号本体 (`decode`)、有限体上の行列演算、零空間計算、誤り位置の共通零点探索、誤り値の復元は曲線パラメータに依存しない共通処理です。

## 定義式

標数2、`c=a+b`、有限体 `GF(2^c)` 上で

\[
\sum_{k=0}^{c-1}\frac{y^{2^{a+k}}}{x^{2^k}}=1
\]

を使います。Frobenius 指数は `GF(2^c)` 上で巡回するため、実装では `(a+k) % c` として評価します。

式を変更する場合、`bbgs_define_equation` だけを別の式に差し替えればよい、というわけではありません。`u,z,w` の定義と Omega 格子の指数条件も同じ曲線モデルに対応している必要があります。したがって、無関係な式に置き換えた場合は `bb_point_data` と `bb_build_basis` も導出し直さなければなりません。

## ビルド

```sh
cc -O2 -std=c11 -Wall -Wextra -Wpedantic -o bbgs_ag_decoder bbgs_ag_decoder.c
```

## 実行

```sh
./bbgs_ag_decoder --a 3 --b 2 --v 149 --t 80 --errors 1 --seed 1 --trials 1
```

- `--a`, `--b`: BBGS 曲線パラメータ
- `--v`, `--t`: ECP に使う divisor/basis パラメータ
- `--errors`: 注入する誤り数
- `--seed`: 再現用乱数 seed
- `--trials`: 試行回数

現在の実装制約は `a=b+1`, `b>=2`, `a+b<=8`, `a` odd, `gcd(a,b)=1` です。この制約範囲で実際に検証した設定は `a=3,b=2`（`GF(32)`）です。したがって、現段階では任意の BBGS パラメータ組を検証済みと主張するものではありません。

## 実装内チェック

起動時に `A*B subset H` を、全ての基底積について評価ベクトルの行空間包含として検査します。復号試験ではランダムな符号語と誤りを作り、復号結果が元の符号語と一致するかを判定します。

`ECP bound estimate` は divisor と基底の仮定に依存する参考値です。実装内の積包含チェックは有用な整合性検査ですが、曲線の絶対既約性・非特異性や全ての理論仮定を証明するものではありません。
