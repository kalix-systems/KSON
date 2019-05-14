/// 0xe0
pub(crate) const MASK_TYPE: u8 = 0b1110_0000;
/// 0x1f
pub(crate) const MASK_META: u8 = 0b0001_1111;
/// 0x00
pub(crate) const TYPE_CON: u8 = 0b0000_0000;
/// Integer type bits, 0x20
pub(crate) const TYPE_INT: u8 = 0b0010_0000;
/// String type bits, 0x40
pub(crate) const TYPE_BYT: u8 = 0b0100_0000;
/// Array type bits, 0x60
pub(crate) const TYPE_ARR: u8 = 0b0110_0000;
/// Map type bits, 0x80
pub(crate) const TYPE_MAP: u8 = 0b1000_0000;
/// Large integer indicator bit, 0x10
pub(crate) const BIG_BIT: u8 = 0b0001_0000;
/// Integer sign bit, 0x0f
pub(crate) const INT_POSITIVE: u8 = 0b0000_1000;

/// Float type bits
pub(crate) const TYPE_FLOAT: u8 = 0b101_00_000;
/// Half-precision tag
pub(crate) const HALF: u8 = TYPE_FLOAT;
/// Single-precision tag
pub(crate) const SINGLE: u8 = TYPE_FLOAT | 0b000_01_000;
/// Double-precision tag
pub(crate) const DOUBLE: u8 = TYPE_FLOAT | 0b000_10_000;

/// [`Null`] pub(crate) constant.
pub(crate) const CON_NULL: u8 = 0b0000_0000;
/// `True` pub(crate) constant.
pub(crate) const CON_TRUE: u8 = 0b0000_0001;
/// `False` pub(crate) constant.
pub(crate) const CON_FALSE: u8 = 0b0000_0010;

pub(crate) const MASK_LEN_BITS: u8 = 0b0000_1111;
pub(crate) const MASK_INT_LEN_BITS: u8 = 0b0000_0111;

pub(crate) const BIGINT_MIN_LEN: u64 = MASK_INT_LEN_BITS as u64 + 2;
pub(crate) const BIGCOL_MIN_LEN: u64 = MASK_LEN_BITS as u64 + 1;
