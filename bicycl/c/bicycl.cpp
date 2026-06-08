#include <memory>
#include "bicycl/arith/qfi.hpp"

using namespace BICYCL;

// https://gmplib.org/manual/Integer-Import-and-Export
static const int MPZ_LE = -1;

static uint8_t* mpz_to_le_bytes(const mpz_srcptr op, uint32_t* len, bool* is_negative = nullptr) {
  // 1 + log2(op).div_ceil(8)
  // The `1 +` ensures this isn't a zero-sized allocation
  void* buf = malloc(1 + ((mpz_sizeinbase(op, 2) + 7) / 8));
  if (!buf)
    abort();
  size_t actual_len;
  mpz_export(buf, &actual_len, MPZ_LE, 1, MPZ_LE, 0, op);
  *len = actual_len;
  if (is_negative)
    *is_negative = mpz_sgn(op) == -1;
  return (uint8_t*) buf;
}

static Mpz mpz_from_le_bytes(uint8_t* const le_bytes, uint32_t const len, bool const is_negative) {
  // We convert to a big-endian vector here because upstream doesn't show a clear way of
  // converting from little endian bytes. Upstream does have a way to construct from a vector.
  std::vector<unsigned char> be_bytes_vector;
  be_bytes_vector.reserve(len);
  for (uint32_t i = len; i > 0; --i)
    be_bytes_vector.push_back(static_cast<unsigned char>(le_bytes[i - 1]));
  Mpz mpz(be_bytes_vector);
  if (is_negative)
    mpz.neg();
  return mpz;
}

class QFIWrapper : public QFI {
  std::shared_ptr<Mpz> L_;

  public:
    QFIWrapper() {}

    QFIWrapper(QFIWrapper* existing) {
      a_ = Mpz(existing->a_);
      b_ = Mpz(existing->b_);
      c_ = Mpz(existing->c_);
      L_ = existing->L_;
    }

    QFIWrapper(Mpz a, Mpz b, Mpz c) {
      a_ = a;
      b_ = b;
      c_ = c;
      L_ = std::shared_ptr<Mpz>(new Mpz(ClassGroup(this->discriminant()).default_nucomp_bound()));
    }

    QFIWrapper(Mpz a, Mpz b, Mpz discriminant, bool _from_discriminant) {
      a_ = a;
      b_ = b;
      c_ = Mpz();
      set_c_from_disc(discriminant);
      L_ = std::shared_ptr<Mpz>(new Mpz(ClassGroup(discriminant).default_nucomp_bound()));
    }

    QFIWrapper* qfi_double() {
      QFIWrapper* result = new QFIWrapper();
      nudupl(*result, *((QFIWrapper* const) this), *L_);
      result->L_ = std::shared_ptr<Mpz>(L_);
      return result;
    }

    QFIWrapper* add(QFIWrapper* const b) {
      QFIWrapper* result = new QFIWrapper();
      nucomp(*result, *((QFIWrapper* const) this), *b, *L_, 0);
      result->L_ = std::shared_ptr<Mpz>(L_);
      return result;
    }

    QFIWrapper* sub(QFIWrapper* const b) {
      QFIWrapper* result = new QFIWrapper();
      nucomp(*result, *((QFIWrapper* const) this), *b, *L_, 1);
      result->L_ = std::shared_ptr<Mpz>(L_);
      return result;
    }
};

void cleanup_qfi(QFIWrapper* const qfi) {
  delete qfi;
}

extern "C" {
  void* rust_bicycl_identity_bicycl_qfi(
    uint8_t* const discriminant_abs_le_bytes, uint32_t const discriminant_abs_len
  ) {
    const Mpz discriminant = mpz_from_le_bytes(discriminant_abs_le_bytes, discriminant_abs_len, true/*is_negative*/);
    QFI one = ClassGroup(discriminant).one();
    return ((void*) new QFIWrapper(one.a(), one.b(), one.c()));
  }

  void* rust_bicycl_new_bicycl_qfi(
    uint8_t* const a_le_bytes, uint32_t const a_len,
    uint8_t* const b_le_bytes, uint32_t const b_len, bool const b_is_negative,
    uint8_t* const c_le_bytes, uint32_t const c_len
  ) {
    const Mpz a = mpz_from_le_bytes(a_le_bytes, a_len, false/*is_negative*/);
    const Mpz b = mpz_from_le_bytes(b_le_bytes, b_len, b_is_negative);
    const Mpz c = mpz_from_le_bytes(c_le_bytes, c_len, false/*is_negative*/);
    return (void*) (new QFIWrapper(a, b, c));
  }

  void* rust_bicycl_new_bicycl_qfi_discriminant(
    uint8_t* const a_le_bytes, uint32_t const a_len,
    uint8_t* const b_le_bytes, uint32_t const b_len, bool const b_is_negative,
    uint8_t* const discriminant_abs_le_bytes, uint32_t const discriminant_abs_len
  ) {
    const Mpz a = mpz_from_le_bytes(a_le_bytes, a_len, false/*is_negative*/);
    const Mpz b = mpz_from_le_bytes(b_le_bytes, b_len, b_is_negative);
    const Mpz discriminant = mpz_from_le_bytes(discriminant_abs_le_bytes, discriminant_abs_len, true/*is_negative*/);
    return (void*) (new QFIWrapper(a, b, discriminant, true));
  }

  uint8_t* rust_bicycl_qfi_a(void* const qfi, uint32_t* len) {
    return mpz_to_le_bytes(mpz_srcptr(((QFIWrapper* const) qfi)->a()), len);
  }

  uint8_t* rust_bicycl_qfi_b(void* const qfi, uint32_t* len, bool* is_negative) {
    return mpz_to_le_bytes(mpz_srcptr(((QFIWrapper* const) qfi)->b()), len, is_negative);
  }

  uint8_t* rust_bicycl_qfi_c(void* const qfi, uint32_t* len) {
    return mpz_to_le_bytes(mpz_srcptr(((QFIWrapper* const) qfi)->c()), len);
  }

  uint8_t* rust_bicycl_qfi_discriminant_abs(void* const qfi, uint32_t* len) {
    return mpz_to_le_bytes(mpz_srcptr(((QFIWrapper* const) qfi)->discriminant()), len);
  }

  void rust_bicycl_qfi_delete(void* qfi) {
    cleanup_qfi((QFIWrapper* const) qfi);
  }

  void rust_bicycl_free(void* buf) {
    free(buf);
  }

  void* rust_bicycl_qfi_clone(void* qfi) {
    return new QFIWrapper((QFIWrapper*)(qfi));
  }

  void rust_bicycl_qfi_neg(void* qfi) {
    ((QFIWrapper*)(qfi))->neg();
  }

  void rust_bicycl_qfi_is_identity(void* const qfi, bool* is_identity) {
    *is_identity = ((QFIWrapper* const) qfi)->is_one();
  }

  void* rust_bicycl_qfi_double(void* const qfi) {
    return ((QFIWrapper* const) qfi)->qfi_double();
  }

  void* rust_bicycl_qfi_add(void* const a, void* const b) {
    return ((QFIWrapper* const) a)->add((QFIWrapper* const) b);
  }

  void* rust_bicycl_qfi_sub(void* const a, void* const b) {
    return ((QFIWrapper* const) a)->sub((QFIWrapper* const) b);
  }
}
