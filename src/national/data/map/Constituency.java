package national.data.map;

import java.io.Serializable;
import national.ElectionConstants;

/**
 * @author Ólavur Kjølbro
 */
public /*@ nullable_by_default @*/ class Constituency implements Serializable {
	
	private static final long serialVersionUID = 1L;

	private int constituency_id;
	private Province province;
	private String name;
	private int constituency_seats;
	private boolean bornholm;

	//@ invariant constituency_id > 0;
	//@ invariant province != null;
	//@ invariant name != null;
	//@ invariant constituency_seats > 0;
	//@ invariant constituency_seats <= ElectionConstants.CONSTITUENCY_SEATS;
	//@ invariant bornholm == true ==> constituency_seats >= 2;


	/**
	 * @param constit_id Id of constituency in database
	 * @param province Province to which constituency belongs
	 * @param name Name of constituency
	 * @param seats_constit No of constituency seats is has 
	 */
	//@ pre constit_id > 0;
	//@ pre seats_constit > 0;
	//@ pre seats_constit <= ElectionConstants.CONSTITUENCY_SEATS;
	//@ post constituency_id == constit_id;
	//@ post constituency_seats == seats_constit;
	//@ post province == prov;
	//@ post name == nam;
	public Constituency (int constit_id, /*@ non_null @*/ Province prov, 
			/*@ non_null @*/ String nam, int seats_constit, boolean bh) {
		this.constituency_id = constit_id;
		this.name = nam;
		this.province = prov;
		this.constituency_seats = seats_constit;
		this.bornholm = bh;
	}

	/**
	 * @return The id of the constituency (in the database)
	 */
	public /*@ pure @*/ int getConstituencyId() {
		return constituency_id;
	}

	/**
	 * @return The name of the constituency
	 */
	public /*@ pure @*/ String getName() {
		return name;
	}

	/**
	 * @return The province to which the constituency belongs 
	 */
	public /*@ pure @*/ Province getProvince() {
		return province;
	}

	/**
	 * @return No of constituency seats of this constituency
	 */
	public /*@ pure @*/ int getConstituencySeats() {
		return constituency_seats;
	}

	/**
	 * @return the bornholm
	 */
	public /*@ pure @*/ boolean isBornholm() {
		return bornholm;
	}
	
	/**
	 * @return  A string informing about the instance
	 */
	@Override
	public /*@ pure @*/ String toString() {
		@SuppressWarnings("unused")
		int i = ElectionConstants.SEATS_GREENLAND;
		return "Constituency - name: "+name+";province: "+province.getName()+";constituency seats: "+constituency_seats+";bornholm: "+bornholm;
	}
}