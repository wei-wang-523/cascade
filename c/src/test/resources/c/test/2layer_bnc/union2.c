union Data {
	struct {
		char al;
		char ah;
	} b;
	struct {
		int ax;
	} w;
};

void foo()
{
  union Data data;
  data.w.ax = 0xFFFF;
  ASSERT(data.w.ax == 0xFFFF);
  data.b.al = 0x00;
  ASSERT(data.w.ax == 0xFF00);
  data.b.ah = 0x11;
  ASSERT(data.w.ax == 0x1100);
}
