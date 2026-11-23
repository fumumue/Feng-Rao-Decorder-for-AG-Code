# AG-FR-VOTE 外部関数 API

この版では、既存の `ag_frvote.c` の Newton 基底・モノミアルシンドローム・Feng–Rao 多数決復号を、別の C プログラムから関数として呼び出せます。

## 1. ビルド

```sh
make
```

生成物:

- `libag_frvote.a` : 外部プログラムからリンクする静的ライブラリ
- `ag_frvote.h` : 公開 API
- `ag_frvote` : 従来どおりのコマンドライン実行ファイル
- `external_caller` : 呼び出し例兼テスト

## 2. 公開関数

```c
int ag_frvote_decode(
    int argc, char **argv,
    const uint16_t *received, size_t received_len,
    size_t *error_positions, uint16_t *error_values,
    size_t output_capacity, size_t *error_count
);
```

- `argv`: 曲線・有限体・訂正半径などの指定。`argv[0]` はプログラム名。
- `received`: 呼び出し側が用意した受信語。GF(2^m) の元を `uint16_t` の多項式基底表現で格納する。
- `received_len`: 受信語の長さ。
- `error_positions`, `error_values`: 復号結果の出力配列。
- `output_capacity`: 出力配列の要素数。
- `error_count`: 実際に回収した誤り数。

成功時は `0` を返します。返却される誤り値は、受信語から復元した誤り値です。したがって、訂正後の語は `received[position] XOR error_value` で得られます（標数2）。

### 戻り値

| 戻り値 | 意味 |
|---:|---|
| `0` | 復号成功 |
| `-1` | API 引数不正 |
| `-10` | API 復号まで到達しなかった |
| `1` | 曲線・パラメータ・セットアップエラー |
| `2` | 復号失敗、または誤り値を確定できない |
| `3` | 出力配列の容量不足 |

## 3. 呼び出し例

`external_caller.c` が実例です。要点は次のとおりです。

```c
#include "ag_frvote.h"
#include <stdint.h>
#include <stddef.h>

uint16_t received[1009] = {0};
size_t positions[16];
uint16_t values[16];
size_t error_count = 0;

/* 例として位置5に値7の誤りを加えた受信語 */
received[5] = 7;

char a0[] = "my_program";
char a1[] = "--m", a2[] = "6";
char a3[] = "--q", a4[] = "4";
char a5[] = "--errors", a6[] = "2"; /* 設計上の訂正半径 */
char a7[] = "--M", a8[] = "250";
char a9[] = "-frvote";
char *opts[] = {a0,a1,a2,a3,a4,a5,a6,a7,a8,a9};

int rc = ag_frvote_decode(
    (int)(sizeof opts / sizeof opts[0]), opts,
    received, 1009,
    positions, values, 16, &error_count
);
```

リンク:

```sh
cc -O2 -std=gnu11 -I. my_program.c libag_frvote.a -o my_program
```

`--errors T` は受信語に含まれる実際の誤り数ではなく、復号器が前提とする訂正半径です。`--M` はシンドローム次数上限です。指定した曲線・種数・点数に対して必要な範囲を満たす必要があります。

この API は `-frvote` を指定し、`-fr`, `-bms`, `-vote` を同時に指定しないでください。FR-VOTE は Newton モノミアルシンドローム経路を使います。

## 4. 受信語の評価点順序

この実装の affine 点列挙順は、有限体の整数表現について `x=0..2^m-1` の外側ループ、`y=0..2^m-1` の内側ループです。その順で曲線式 `F(x,y)=0` を満たす点だけを並べます。

- `received_len` が `--len` 適用後の affine 点数（Laurent 基底で除外される軸上の点を含む）なら、API が必要な点を内部で除外し、返却位置を元の affine 点列の添字に戻します。
- `received_len` が Laurent 基底用の軸上点除外後の長さなら、呼び出し側で同じ順序に除外した配列として扱います。返却位置はその配列内の添字です。
- `--len` で puncture する場合、入力配列もその `--len` までの先頭点に対応させてください。
- 自動長さ上限（8192）が適用される曲線では、入力長と一致させるため `--len` を明示してください。

符号器と復号器で評価点順序・除外規則が一致していることが必要です。

## 5. 現在の制約

- 現時点で公開した復号 API は one-point Newton FR-VOTE です。多点 BASIC、FR、BMS、VOTE はまだこの受信語 API には接続していません。
- 既存コードの大規模なファイルスコープ作業領域をそのまま利用しているため、**同一プロセス内での複数回呼び出し、並列呼び出し、スレッドセーフ性は保証しません**。現在は1プロセスにつき1回の呼び出しを前提にしてください。
- API の受信語は「誤りを含む評価語」です。符号語そのものを渡すのではなく、符号語に誤りを加えた後の値を渡します。
- `uint16_t` の値は `0..2^m-1` の範囲である必要があります。

## 6. テスト

```sh
make test
```

テストは GF(2^6)、BBGS `q=4`、`g=123` の設定で次を検査します。

1. 誤りなし
2. 位置5、誤り値7の1誤り
3. 位置5/99、誤り値7/31の2誤り

全ケースで、復号位置と誤り値が注入値に一致することを確認します。
