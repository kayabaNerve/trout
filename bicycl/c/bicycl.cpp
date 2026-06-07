#include <memory>
#include "bicycl/arith/qfi.hpp"

using namespace BICYCL;

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
    uint8_t* const discriminant_abs_be_bytes, uint32_t const discriminant_abs_len
  ) {
    Mpz discriminant = Mpz();
    for (uint32_t i = 0; i < (8 * discriminant_abs_len); i++) {
      if ((discriminant_abs_be_bytes[i / 8] >> (7 - (i % 8))) & 1) {
        size_t bit = (discriminant_abs_len * 8) - (i + 1);
        discriminant.setbit(bit);
      }
    }
    discriminant.neg();

    QFI one = ClassGroup(discriminant).one();
    return ((void*) new QFIWrapper(one.a(), one.b(), one.c()));
  }

  void* rust_bicycl_new_bicycl_qfi(
    uint8_t* const a_be_bytes, uint32_t const a_len,
    uint8_t* const b_be_bytes, uint32_t const b_len, bool const b_is_negative,
    uint8_t* const c_be_bytes, uint32_t const c_len
  ) {
    Mpz a = Mpz();
    for (uint32_t i = 0; i < (8 * a_len); i++) {
      if ((a_be_bytes[i / 8] >> (7 - (i % 8))) & 1) {
        size_t bit = (a_len * 8) - (i + 1);
        a.setbit(bit);
      }
    }
    Mpz b = Mpz();
    for (uint32_t i = 0; i < (8 * b_len); i++) {
      if ((b_be_bytes[i / 8] >> (7 - (i % 8))) & 1) {
        size_t bit = (b_len * 8) - (i + 1);
        b.setbit(bit);
      }
    }
    if (b_is_negative) {
      b.neg();
    }
    Mpz c = Mpz();
    for (uint32_t i = 0; i < (8 * c_len); i++) {
      if ((c_be_bytes[i / 8] >> (7 - (i % 8))) & 1) {
        size_t bit = (c_len * 8) - (i + 1);
        c.setbit(bit);
      }
    }
    return (void*) (new QFIWrapper(a, b, c));
  }

  void* rust_bicycl_new_bicycl_qfi_discriminant(
    uint8_t* const a_be_bytes, uint32_t const a_len,
    uint8_t* const b_be_bytes, uint32_t const b_len, bool const b_is_negative,
    uint8_t* const discriminant_abs_be_bytes, uint32_t const discriminant_abs_len
  ) {
    Mpz a = Mpz();
    for (uint32_t i = 0; i < (8 * a_len); i++) {
      if ((a_be_bytes[i / 8] >> (7 - (i % 8))) & 1) {
        size_t bit = (a_len * 8) - (i + 1);
        a.setbit(bit);
      }
    }
    Mpz b = Mpz();
    for (uint32_t i = 0; i < (8 * b_len); i++) {
      if ((b_be_bytes[i / 8] >> (7 - (i % 8))) & 1) {
        size_t bit = (b_len * 8) - (i + 1);
        b.setbit(bit);
      }
    }
    if (b_is_negative) {
      b.neg();
    }
    Mpz discriminant = Mpz();
    for (uint32_t i = 0; i < (8 * discriminant_abs_len); i++) {
      if ((discriminant_abs_be_bytes[i / 8] >> (7 - (i % 8))) & 1) {
        size_t bit = (discriminant_abs_len * 8) - (i + 1);
        discriminant.setbit(bit);
      }
    }
    discriminant.neg();
    return (void*) (new QFIWrapper(a, b, discriminant, true));
  }

  uint8_t* rust_bicycl_qfi_a(void* const qfi, uint32_t* len) {
    // 1 + log2(a).div_ceil(8)
    // The `1 +` ensures this isn't a zero-sized allocation
    void* buf = malloc(1 + ((mpz_sizeinbase(mpz_srcptr(((QFIWrapper* const) qfi)->a()), 2) + 7) / 8));
    size_t actual_len;
    mpz_export(buf, &actual_len, 1, 1, 1, 0, mpz_srcptr(((QFIWrapper* const) qfi)->a()));
    *len = actual_len;
    return (uint8_t*) buf;
  }

  uint8_t* rust_bicycl_qfi_b(void* const qfi, uint32_t* len, bool* is_negative) {
    void* buf = malloc(1 + ((mpz_sizeinbase(mpz_srcptr(((QFIWrapper* const) qfi)->b()), 2) + 7) / 8));
    size_t actual_len;
    mpz_export(buf, &actual_len, 1, 1, 1, 0, mpz_srcptr(((QFIWrapper* const) qfi)->b()));
    *len = actual_len;
    if (mpz_sgn(mpz_srcptr(((QFIWrapper* const) qfi)->b())) == -1) {
      *is_negative = true;
    } else {
      *is_negative = false;
    }
    return (uint8_t*) buf;
  }

  uint8_t* rust_bicycl_qfi_c(void* const qfi, uint32_t* len) {
    // 1 + log2(a).div_ceil(8)
    // The `1 +` ensures this isn't a zero-sized allocation
    void* buf = malloc(1 + ((mpz_sizeinbase(mpz_srcptr(((QFIWrapper* const) qfi)->c()), 2) + 7) / 8));
    size_t actual_len;
    mpz_export(buf, &actual_len, 1, 1, 1, 0, mpz_srcptr(((QFIWrapper* const) qfi)->c()));
    *len = actual_len;
    return (uint8_t*) buf;
  }

  uint8_t* rust_bicycl_qfi_discriminant_abs(void* const qfi, uint32_t* len) {
    // 1 + log2(a).div_ceil(8)
    // The `1 +` ensures this isn't a zero-sized allocation
    void* buf = malloc(1 + ((mpz_sizeinbase(mpz_srcptr(((QFIWrapper* const) qfi)->discriminant()), 2) + 7) / 8));
    size_t actual_len;
    mpz_export(buf, &actual_len, 1, 1, 1, 0, mpz_srcptr(((QFIWrapper* const) qfi)->discriminant()));
    *len = actual_len;
    return (uint8_t*) buf;
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
