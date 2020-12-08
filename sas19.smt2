/* ; SAS19 */

(forall (m: int) (n: int). m <= 0 \/ F n m) /\
(forall (m: int) (n: int).
(forall (rec!_F2: int). rec!_F2 < 1 * m + 1 \/ rec!_F2 < -1 * m + 1 \/ rec!_F2 < 1 * n + 1 \/ rec!_F2 < -1 * n + 1 \/ F2 rec!_F2 n m) \/ m > 0)
where


F2 (rec!_F2: int) (x: int) (y: int): bool =nu
  rec!_F2 > 0 /\ (A2 x y \/ B2 x y \/ x <= 0 /\ F2 (rec!_F2 - 1) (x + y) y \/ x > 0 /\ F2 (rec!_F2 - 1) (x - y) y);


B2 (x: int) (y: int): bool =nu x > 0 /\ B2 (x - y) y;
A2 (x: int) (y: int): bool =nu x <= 0 /\ A2 (x + y) y;


F (x: int) (y: int): bool =nu (forall (rec!_A: int). rec!_A < 1 * y + 1 \/ rec!_A < -1 * y + 1 \/ rec!_A < 1 * x + 1 \/ rec!_A < -1 * x + 1 \/ A rec!_A x y) /\ (forall (rec!_B: int). rec!_B < 1 * y + 1 \/ rec!_B < -1 * y + 1 \/ rec!_B < 1 * x + 1 \/ rec!_B < -1 * x + 1 \/ B rec!_B x y) /\ (x > 0 \/ F (x + y) y) /\ (x <= 0 \/ F (x - y) y);


B (rec!_B: int) (x: int) (y: int): bool =nu rec!_B > 0 /\ (x <= 0 \/ B (rec!_B - 1) (x - y) y);
A (rec!_A: int) (x: int) (y: int): bool =nu rec!_A > 0 /\ (x > 0 \/ A (rec!_A - 1) (x + y) y);