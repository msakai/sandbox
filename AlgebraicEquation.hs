
import Data.Complex

-- Solve the equation ax³ + bx² + cx + d = 0
solveCubicEquation :: (RealFloat a) => Complex a -> Complex a -> Complex a -> Complex a -> (Complex a, Complex a, Complex a)
solveCubicEquation a b c d =
  -- x³ + a₂ x² + a₁ x + a₀ = 0
  -- x = y - a₂ / 3
  -- y³ + (a₁ - a₂² / 3) y + (a₀ - a₁ a₂ / 3 + 2a₂³ / 27) = 0
  case solveCubicEquation' (a₁ - a₂**2 / 3) (a₀ - a₁*a₂ / 3 + 2 * a₂**3 / 27) of
    (y1, y2, y3) -> (f y1, f y2, f y3)
  where
    a₂ = b / a
    a₁ = c / a
    a₀ = d / a
    f y = y - a₂ / 3

-- Solve the equation x³ + px + q = 0 using Cardano's formula
--
-- https://en.wikipedia.org/wiki/Cubic_equation#Cardano's_formula
solveCubicEquation' :: (RealFloat a) => Complex a -> Complex a -> (Complex a, Complex a, Complex a)
solveCubicEquation' p q = (u1 + v1, u2 + v2, u3 + v3)
  where
    -- Let x = u + v
    -- x³ + px + q = 0
    -- ⇔ x³ = u³ + 3u²v + 3uv² + v³
    -- ⇔ x³ - 3uv (u + v) - (u³ + v³) = 0
    -- ⇔ x³ - 3uv x - (u³ + v³) = 0
    -- Thus, p = -3uv and q = - (u³ + v³)
    -- uv = -p/3 and u³ + v³ = - q
    -- u³ and v³ are solutions of the equation y² + qy - (p/3)³
    (u³, v³) = solveQuadraticEquation 1 q (- (p / 3)**3)
    ω = (- 1/2) :+ (sqrt 3 / 2)
    u1 = u³ ** (1/3)
    u2 = u1 * ω
    u3 = u2 * ω
    v1 = (- p / 3) / u1
    v2 = (- p / 3) / u2
    v3 = (- p / 3) / u3

-- Solve the equation ax² + bx + c = 0
solveQuadraticEquation :: (RealFloat a) => Complex a -> Complex a -> Complex a -> (Complex a, Complex a)
solveQuadraticEquation a b c =
  ( (- b + sqrt (b**2 - 4*a*c)) / (2*a)
  , (- b - sqrt (b**2 - 4*a*c)) / (2*a)
  )

test =
  case solveCubicEquation' p q of
    (x1, x2, x3) -> [(x, x ** 3 + p * x + q) | x <- [x1,x2,x3]]
  where
    p = 6
    q = -20

test2 =
  case solveCubicEquation 1 0 p q of
    (x1, x2, x3) -> [(x, x ** 3 + p * x + q) | x <- [x1,x2,x3]]
  where
    p = 6
    q = -20
