
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

-- Solve the quartic equation ax⁴ + bx³ + cx² + dx + e = 0 using Ferrari's solution
solveQuarticEquation :: (RealFloat a) => Complex a -> Complex a -> Complex a -> Complex a -> Complex a -> (Complex a, Complex a, Complex a, Complex a)
solveQuarticEquation a b c d e =
  case solveQuarticEquation' p q r of
    (y1, y2, y3, y4) -> (f y1, f y2, f y3, f y4)
  where
    -- ax⁴ + bx³ + cx² + dx + e = 0 ⇔ x⁴ + a₃x³ + a₂x² + a₁x + a₀ = 0
    a₃ = b / a
    a₂ = c / a
    a₁ = d / a
    a₀ = e / a

    {-
       Let x = y - a₃/4
       x⁴ + a₃x³ + a₂x² + a₁x + a₀ = 0
       ⇔ (y - a₃/4)⁴ + a₃(y - a₃/4)³ + a₂(y - a₃/4)² + a₁(y - a₃/4) + a₀ = 0
       ⇔ y⁴ + (-(3/8) a₃² + a₂) y² + (a₃³ / 8 - a₃ a₂ / 2 + a₁) y + ((-3/256) a₃⁴ + a₃² a₂ / 16 - a₃ a₁ / 4 + a₀)
       ⇔ y⁴ + p y² + q y + r
     -}
    f y = y - a₃ / 4
    p = (-3/8) * a₃**2 + a₂
    q = a₃**3 / 8 - a₃*a₂ / 2 + a₁
    r = (-3/256) * a₃**4 + a₃**2 * a₂ / 16 - a₃ * a₁ / 4 + a₀

-- Solve the quartic equation x⁴ + px² + qx + r = 0
solveQuarticEquation' :: (RealFloat a) => Complex a -> Complex a -> Complex a -> (Complex a, Complex a, Complex a, Complex a)
solveQuarticEquation' p q r =
  {-
  x⁴ + px² + qx + r = 0
  x⁴ = - px² - qx - r
  (x² + l)² = (2l - p)x² - qx + (l² - r)

  -- Discriminant of (2l - p)x² - qx + (l² - r)
  D = 0
  q² -  4 (2l - p) (l² - r) = 0
  8l³ - 4 pl² - 8rl + (4pr - q²) = 0
  -}
  case solveCubicEquation 8 (-4*p) (-8*r) (4*p*r - q*q) of
    (l, _l2, _l3) ->
      {-
        q² -  4 (2l - p) (l² - r) = 0
        l² - r = q² / 4(2l - p)

        (x² + l)² = (2l - p)x² - qx + (l² - r)
                  = (2l - p)x² - qx + q² / 4(2l - p)
                  = (√(2l - p) x - (q / 2(√(2l - p))))²
                  = (m x + n)²
                  where
                    m = √(2l - p)
                    n = - q / 2(√(2l - p))
        x² + l = ± (m x + n)
        x² ∓ m x + (l ∓ n) = 0
      -}
      let m = sqrt (2*l - p)
          n = - q / (2*m)
       in case (solveQuadraticEquation 1 (- m) (l - n), solveQuadraticEquation 1 m (l + n)) of
            ((x1, x2), (x3, x4)) -> (x1, x2, x3, x4)

-- ------------------------------------------------------------------------

test_solveCubicEquation' =
  case solveCubicEquation' p q of
    (x1, x2, x3) -> and [magnitude (x ** 3 + p * x + q) <= 1e-10 | x <- [x1,x2,x3]]
  where
    p = 6
    q = -20

test_solveCubicEquation =
  case solveCubicEquation 1 0 p q of
    (x1, x2, x3) -> and [magnitude (x ** 3 + p * x + q) <= 1e-10 | x <- [x1,x2,x3]]
  where
    p = 6
    q = -20

test_solveQuarticEquation' =
  case solveQuarticEquation' p q r of
    (x1, x2, x3, x4) -> and [magnitude (x ** 4 + p * x ** 2 + q * x + r) <= 1e-10 | x <- [x1,x2,x3,x4]]
  where
    p = -2
    q = -8
    r = -3

test_solveQuarticEquation =
  case solveQuarticEquation 1 0 p q r of
    (x1, x2, x3, x4) -> and [magnitude (x ** 4 + p * x ** 2 + q * x + r) <= 1e-10 | x <- [x1,x2,x3,x4]]
  where
    p = -2
    q = -8
    r = -3

test_solveQuarticEquation'_biquadratic =
  case solveQuarticEquation' (-8) 0 16 of
    (x1, x2, x3, x4) -> and [magnitude (x ** 4 + p * x ** 2 + q * x + r) <= 1e-10 | x <- [x1,x2,x3,x4]]
  where
    p = -8
    q = 0
    r = 16

-- https://science-log.com/%E6%95%B0%E5%AD%A6/4%E6%AC%A1%E6%96%B9%E7%A8%8B%E5%BC%8F%E3%81%AE%E8%A7%A3%E3%81%AE%E5%85%AC%E5%BC%8F%EF%BC%88ferrari%E3%81%AE%E8%A7%A3%E6%B3%95%EF%BC%89/
test_solveQuarticEquation_2 =
  case solveQuarticEquation 1 a b c d of
    (x1, x2, x3, x4) -> and [magnitude (x ** 4 + a * x**3 + b * x**2 +  c * x + d) <= 1e-10 | x <- [x1,x2,x3,x4]]
  where
    a = -8
    b = 28
    c = -80
    d = 48

-- https://science-log.com/%E6%95%B0%E5%AD%A6/4%E6%AC%A1%E6%96%B9%E7%A8%8B%E5%BC%8F%E3%81%AE%E8%A7%A3%E3%81%AE%E5%85%AC%E5%BC%8F%EF%BC%88ferrari%E3%81%AE%E8%A7%A3%E6%B3%95%EF%BC%89/
test_solveQuarticEquation_3 =
  case solveQuarticEquation 1 a b c d of
    (x1, x2, x3, x4) -> and [magnitude (x ** 4 + a * x**3 + b * x**2 +  c * x + d) <= 1e-10 | x <- [x1,x2,x3,x4]]
  where
    a = 4
    b = 8
    c = 0
    d = -9

-- https://science-log.com/%E6%95%B0%E5%AD%A6/4%E6%AC%A1%E6%96%B9%E7%A8%8B%E5%BC%8F%E3%81%AE%E8%A7%A3%E3%81%AE%E5%85%AC%E5%BC%8F%EF%BC%88ferrari%E3%81%AE%E8%A7%A3%E6%B3%95%EF%BC%89/
test_solveQuarticEquation_4 =
  case solveQuarticEquation 1 a b c d of
    (x1, x2, x3, x4) -> and [magnitude (x ** 4 + a * x**3 + b * x**2 +  c * x + d) <= 1e-10 | x <- [x1,x2,x3,x4]]
  where
    a = -12
    b = 49
    c = -78
    d = 40

-- ------------------------------------------------------------------------
