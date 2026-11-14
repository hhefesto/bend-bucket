import Base
import ../Bucket.bend as B

# Limit.hs's own rules (5 tries, one each 12 s; 20, one each 3 s): one
# visitor at one instant gets 5 of 7; 22 visitors get 20; a refused visitor
# who waits what it was told is let through.
def pb.v(r: B.bk.R) -> Nat:
  match r:
    case B.bk.R{B.bk.Wait{w}, bs}:
      w
    case B.bk.R{B.bk.Admitted{}, bs}:
      0n

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("burst " ++ Nat.show(B.bk.count(B.bk.rules(), ["v", "v", "v", "v", "v", "v", "v"], 0n, 0n, B.bk.full(B.bk.rules(), 0n))))
    IO.print("together " ++ Nat.show(B.bk.count(B.bk.rules(), ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r", "s", "t", "u", "v"], 0n, 0n, B.bk.full(B.bk.rules(), 0n))))
