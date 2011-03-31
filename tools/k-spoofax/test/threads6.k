function main() {
	spawn {
		var e;
		try {
			try {
				try {
				try {
					var x = 1; write(x); throw ++x;
				} catch(e) {
					write(e);
					throw ++e;
				}
				} catch(e) {
					write(e);
					throw ++e;
				}
			} catch(e) {
				write(e);
				throw ++e;
			}
		} catch(e) {
			write(e);
		}
	}
	spawn {
		var e;
		try {
			try {
				try {
					try {
						var x = 1; write(x); throw ++x;
					} catch(e) {
						write(e);
						throw ++e;
					}
				} catch(e) {
					write(e);
					throw ++e;
				}
			} catch(e) {
				write(e);
				throw ++e;
			}
		} catch(e) {
			write(e);
		}
	}
}