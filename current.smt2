/*
; Current
; SAS19で simplifyするとforallが2つに分かれる？ (これは常に正当ではないはず。本当にやっているか確認)
; Sentry_sub53, Sentry_sub55 がinliningされている。
; 無駄な引数を削る
; boundのつくり方が、小林先生の言ったやつになっている => これの効果がかなりでかいようだ
; 再帰の最後がgreaterか+equalか
; A2, B2の引数の数 => A2, B2のbody以降、他の真に引数を減少させている述語を参照することがなければ不要
; 出力される述語の順番
; 本来、nuであるFの呼び出しはそのままできるはず。しかし、引数の追加に伴い、その初期化が必要になった。
; この場合、Fはより下のレベルの述語 = 既に全てnuになっている述語、しか参照していないので、不要
*/

(forall (n19: int) (m18: int). m18 <= 0 \/ F n19 m18) /\
(forall (n19: int) (m18: int).
(forall (rec!_F2: int). rec!_F2 < 1 * n19 + 1 \/ rec!_F2 < -1 * n19 + 1 \/ rec!_F2 < 1 * m18 + 1 \/ rec!_F2 < -1 * m18 + 1 \/ F2 rec!_F2 n19 m18) \/ m18 > 0)
where

F2 (rec_F241: int) (x21: int) (y22: int): bool =nu
  rec_F241 >= 0 /\ (A2 x21 y22 \/ B2 x21 y22 \/ x21 <= 0 /\ F2 (rec_F241 - 1) (x21 + y22) y22 \/ x21 > 0 /\ F2 (rec_F241 - 1) (x21 - y22) y22);

B2 (x23: int) (y24: int): bool =nu x23 > 0 /\ B2 (x23 - y24) y24;
A2 (x25: int) (y26: int): bool =nu x25 <= 0 /\ A2 (x25 + y26) y26;


B (rec_B34: int) (x29: int) (y30: int): bool =nu rec_B34 >= 0 /\ (x29 <= 0 \/ B (rec_B34 - 1) (x29 - y30) y30);
A (rec_A33: int) (x31: int) (y32: int): bool =nu rec_A33 >= 0 /\ (x31 > 0 \/ A (rec_A33 - 1) (x31 + y32) y32);

F (x27: int) (y28: int): bool =nu (forall (forall_y38: int). forall_y38 < 1 * y28 + 1 \/ forall_y38 < -1 * y28 + 1 \/ forall_y38 < 1 * x27 + 1 \/ forall_y38 < -1 * x27 + 1 \/ A forall_y38 x27 y28) /\ (forall (forall_y38: int). forall_y38 < 1 * y28 + 1 \/ forall_y38 < -1 * y28 + 1 \/ forall_y38 < 1 * x27 + 1 \/ forall_y38 < -1 * x27 + 1 \/ B forall_y38 x27 y28) /\ (x27 > 0 \/ F (x27 + y28) y28) /\ (x27 <= 0 \/ F (x27 - y28) y28);
