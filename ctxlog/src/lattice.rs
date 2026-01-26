use core::cmp::{max, min};

use crate::interner::Interner;
use crate::table::Value;
use crate::ssa::{BinaryOp, UnaryOp};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Interval {
    pub low: i32,
    pub high: i32,
}

impl Interval {
    pub fn top() -> Interval {
        Interval {
            low: i32::MIN,
            high: i32::MAX,
        }
    }

    pub fn bottom() -> Interval {
        Interval {
            low: i32::MAX,
            high: i32::MIN,
        }
    }

    pub fn from(cons: i32) -> Interval {
        Interval {
            low: cons,
            high: cons,
        }
    }

    pub fn union(&self, other: &Interval) -> Interval {
        Interval {
            low: min(self.low, other.low),
            high: max(self.high, other.high),
        }
    }

    pub fn intersect(&self, other: &Interval) -> Interval {
        Interval {
            low: max(self.low, other.low),
            high: min(self.high, other.high),
        }
    }

    pub fn contains(&self, other: &Interval) -> bool {
        self.low <= other.low && self.high >= other.high
    }

    pub fn widen(&self, new: &Interval) -> Interval {
        Interval {
            low: if self.low > new.low {
                i32::MIN
            } else {
                new.low
            },
            high: if self.high < new.high {
                i32::MAX
            } else {
                new.high
            },
        }
    }

    pub fn try_constant(&self) -> Option<i32> {
        if self.low == self.high {
            Some(self.low)
        } else {
            None
        }
    }

    pub fn forward_unary(&self, op: UnaryOp) -> Interval {
        use UnaryOp::*;
        (|| match op {
            Negate => Some(Interval {
                low: self.high.checked_neg()?,
                high: self.low.checked_neg()?,
            }),
            Not => Some({
                if self.low == 0 && self.high == 0 {
                    Interval { low: 1, high: 1 }
                } else if self.low > 0 || self.high < 0 {
                    Interval { low: 0, high: 0 }
                } else {
                    Interval { low: 0, high: 1 }
                }
            }),
        })()
        .unwrap_or(Interval::top())
    }

    pub fn forward_binary(&self, other: &Interval, op: BinaryOp) -> Interval {
        use BinaryOp::*;
        (|| match op {
            Add => Some(Interval {
                low: self.low.checked_add(other.low)?,
                high: self.high.checked_add(other.high)?,
            }),
            Sub => Some(Interval {
                low: self.low.checked_sub(other.high)?,
                high: self.high.checked_sub(other.low)?,
            }),
            Mul => Some(Interval {
                low: min(
                    min(
                        self.low.checked_mul(other.low)?,
                        self.low.checked_mul(other.high)?,
                    ),
                    min(
                        self.high.checked_mul(other.low)?,
                        self.high.checked_mul(other.high)?,
                    ),
                ),
                high: max(
                    max(
                        self.low.checked_mul(other.low)?,
                        self.low.checked_mul(other.high)?,
                    ),
                    max(
                        self.high.checked_mul(other.low)?,
                        self.high.checked_mul(other.high)?,
                    ),
                ),
            }),
            Div | Rem => None,
            EE => Some({
                if let (Some(cons1), Some(cons2)) = (self.try_constant(), other.try_constant())
                    && cons1 == cons2
                {
                    Interval { low: 1, high: 1 }
                } else if self.high < other.low || other.high < self.low {
                    Interval { low: 0, high: 0 }
                } else {
                    Interval { low: 0, high: 1 }
                }
            }),
            NE => Some({
                if let (Some(cons1), Some(cons2)) = (self.try_constant(), other.try_constant())
                    && cons1 == cons2
                {
                    Interval { low: 0, high: 0 }
                } else if self.high < other.low || other.high < self.low {
                    Interval { low: 1, high: 1 }
                } else {
                    Interval { low: 0, high: 1 }
                }
            }),
            LT => Some({
                if self.high < other.low {
                    Interval { low: 1, high: 1 }
                } else if self.low >= other.high {
                    Interval { low: 0, high: 0 }
                } else {
                    Interval { low: 0, high: 1 }
                }
            }),
            LE => Some({
                if self.high <= other.low {
                    Interval { low: 1, high: 1 }
                } else if self.low > other.high {
                    Interval { low: 0, high: 0 }
                } else {
                    Interval { low: 0, high: 1 }
                }
            }),
            GT => Some({
                if self.low > other.high {
                    Interval { low: 1, high: 1 }
                } else if self.high <= other.low {
                    Interval { low: 0, high: 0 }
                } else {
                    Interval { low: 0, high: 1 }
                }
            }),
            GE => Some({
                if self.low >= other.high {
                    Interval { low: 1, high: 1 }
                } else if self.high < other.low {
                    Interval { low: 0, high: 0 }
                } else {
                    Interval { low: 0, high: 1 }
                }
            }),
        })()
        .unwrap_or(Interval::top())
    }
}

impl Interner<Interval> {
    pub fn intersect(&self) -> impl FnMut(Value, Value) -> Value + '_ {
        |a: Value, b: Value| {
            self.intern(self.get(a.into()).intersect(&self.get(b.into())))
                .into()
        }
    }

    pub fn union(&self) -> impl FnMut(Value, Value) -> Value + '_ {
        |a: Value, b: Value| {
            self.intern(self.get(a.into()).union(&self.get(b.into())))
                .into()
        }
    }

    pub fn forward_unary(&self) -> impl FnMut(Value, UnaryOp) -> Value + '_ {
        |a: Value, op: UnaryOp| {
            self.intern(self.get(a.into()).forward_unary(op))
                .into()
        }
    }

    pub fn forward_binary(&self) -> impl FnMut(Value, Value, BinaryOp) -> Value + '_ {
        |a: Value, b: Value, op: BinaryOp| {
            self.intern(self.get(a.into()).forward_binary(&self.get(b.into()), op))
                .into()
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IsZero {
    Top,
    Zero,
    NotZero,
    Bottom,
}

impl IsZero {
    pub fn top() -> IsZero {
        IsZero::Top
    }

    pub fn bottom() -> IsZero {
        IsZero::Bottom
    }

    pub fn leq(&self, other: &IsZero) -> bool {
        use IsZero::*;
        match (*self, *other) {
            (Bottom, _) => true,
            (_, Top) => true,
            _ => *self == *other,
        }
    }

    pub fn meet(&self, other: &IsZero) -> IsZero {
        use IsZero::*;
        match (*self, *other) {
            (Bottom, _) | (_, Bottom) => Bottom,
            (Top, other) | (other, Top) => other,
            _ if *self == *other => *self,
            _ => Bottom,
        }
    }

    pub fn join(&self, other: &IsZero) -> IsZero {
        use IsZero::*;
        match (*self, *other) {
            (Top, _) | (_, Top) => Top,
            (Bottom, other) | (other, Bottom) => other,
            _ if *self == *other => *self,
            _ => Top,
        }
    }

    pub fn forward_unary(&self, op: UnaryOp) -> IsZero {
        use IsZero::*;
        use UnaryOp::*;
        match op {
            Negate => *self,
            Not => match *self {
                Top | Bottom => *self,
                Zero => NotZero,
                NotZero => Zero,
            },
        }
    }

    pub fn backward_unary(&self, op: UnaryOp) -> IsZero {
        self.forward_unary(op)
    }

    pub fn forward_binary(&self, other: &IsZero, op: BinaryOp) -> IsZero {
        use BinaryOp::*;
        use IsZero::*;
        match op {
            Add | Sub => match (*self, *other) {
                (Bottom, _) | (_, Bottom) => Bottom,
                (Zero, other) | (other, Zero) => other,
                _ => Top,
            },
            Mul => match (*self, *other) {
                (Zero, _) | (_, Zero) => Zero,
                (Bottom, _) | (_, Bottom) => Bottom,
                _ => Top,
            },
            Div | Rem => Top,
            EE => match (*self, *other) {
                (Bottom, _) | (_, Bottom) => Bottom,
                (Top, _) | (_, Top) => Top,
                _ if *self == *other => NotZero,
                _ => Zero,
            },
            NE => match (*self, *other) {
                (Bottom, _) | (_, Bottom) => Bottom,
                (Top, _) | (_, Top) => Top,
                _ if *self != *other => NotZero,
                _ => Zero,
            },
            LT | LE | GT | GE => match (*self, *other) {
                (Bottom, _) | (_, Bottom) => Bottom,
                _ => Top,
            },
        }
    }
}

impl From<Value> for IsZero {
    fn from(value: Value) -> Self {
        match value {
            0 => IsZero::Top,
            1 => IsZero::Zero,
            2 => IsZero::NotZero,
            3 => IsZero::Bottom,
            _ => panic!(),
        }
    }
}

impl From<IsZero> for Value {
    fn from(iz: IsZero) -> Self {
        match iz {
            IsZero::Top => 0,
            IsZero::Zero => 1,
            IsZero::NotZero => 2,
            IsZero::Bottom => 3,
        }
    }
}
