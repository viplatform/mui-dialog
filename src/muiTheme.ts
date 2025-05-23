import { createTheme } from "@mui/material";
import { textStyles } from "./theme.constant";

export const dialogTypography = {
  fontFamily:
    "-apple-system,system-ui,BlinkMacSystemFont,Segoe UI,Roboto,Helvetica Neue,Fira Sans,Ubuntu,Oxygen,Oxygen Sans,Cantarell,Droid Sans,Apple Color Emoji,Segoe UI Emoji,Segoe UI Emoji,Segoe UI Symbol,Lucida Grande,Helvetica,Arial,sans-serif",

  displayL: {
    fontSize: "80px",
    fontWeight: textStyles.fontWeight.semibold,
    lineHeight: "92px",
    letterSpacing: textStyles.letterSpacing.default,
  },
  displayM: {
    fontSize: "40px",
    fontWeight: textStyles.fontWeight.semibold,
    lineHeight: "52px",
    letterSpacing: textStyles.letterSpacing.default,
  },

  headingL: {
    fontSize: "32px",
    fontWeight: textStyles.fontWeight.semibold,
    lineHeight: "44px",
    letterSpacing: textStyles.letterSpacing.default,
  },
  headingM: {
    fontSize: "28px",
    fontWeight: textStyles.fontWeight.semibold,
    lineHeight: "40px",
    letterSpacing: textStyles.letterSpacing.default,
  },
  headingS: {
    fontSize: "24px",
    fontWeight: textStyles.fontWeight.semibold,
    lineHeight: "36px",
    letterSpacing: textStyles.letterSpacing.default,
  },

  semiBoldLabelL: {
    fontSize: "20px",
    lineHeight: "28px",
    fontWeight: textStyles.fontWeight.semibold,
    letterSpacing: textStyles.letterSpacing.default,
  },
  semiBoldLabelM: {
    fontSize: "16px",
    lineHeight: "24px",
    fontWeight: textStyles.fontWeight.semibold,
    letterSpacing: textStyles.letterSpacing.default,
  },
  semiBoldLabelS: {
    fontSize: "14px",
    lineHeight: "20px",
    fontWeight: textStyles.fontWeight.semibold,
    letterSpacing: textStyles.letterSpacing.default,
  },
  semiBoldLabelXs: {
    fontSize: "12px",
    lineHeight: "16px",
    fontWeight: textStyles.fontWeight.semibold,
    letterSpacing: textStyles.letterSpacing.default,
  },
  semiBoldLabelXxs: {
    fontSize: "10px",
    lineHeight: "14px",
    fontWeight: textStyles.fontWeight.semibold,
    letterSpacing: textStyles.letterSpacing.default,
  },

  regularLabelL: {
    fontSize: "20px",
    lineHeight: "28px",
    fontWeight: textStyles.fontWeight.regular,
    letterSpacing: textStyles.letterSpacing.default,
  },
  regularLabelM: {
    fontSize: "16px",
    lineHeight: "24px",
    fontWeight: textStyles.fontWeight.regular,
    letterSpacing: textStyles.letterSpacing.default,
  },
  regularLabelS: {
    fontSize: "14px",
    lineHeight: "20px",
    fontWeight: textStyles.fontWeight.regular,
    letterSpacing: textStyles.letterSpacing.default,
  },
  regularLabelXs: {
    fontSize: "12px",
    lineHeight: "16px",
    fontWeight: textStyles.fontWeight.regular,
    letterSpacing: textStyles.letterSpacing.default,
  },
  regularLabelXxs: {
    fontSize: "10px",
    lineHeight: "14px",
    fontWeight: textStyles.fontWeight.regular,
    letterSpacing: textStyles.letterSpacing.default,
  },

  textXl: {
    fontSize: "20px",
    fontWeight: textStyles.fontWeight.regular,
    lineHeight: "28px",
    letterSpacing: textStyles.letterSpacing.default,
  },
  textL: {
    fontSize: "16px",
    fontWeight: textStyles.fontWeight.regular,
    lineHeight: "24px",
    letterSpacing: textStyles.letterSpacing.default,
  },
  textM: {
    fontSize: "14px",
    fontWeight: textStyles.fontWeight.regular,
    lineHeight: "20px",
    letterSpacing: textStyles.letterSpacing.default,
  },

  subtextM: {
    fontSize: "12px",
    fontWeight: textStyles.fontWeight.regular,
    lineHeight: "16px",
    letterSpacing: textStyles.letterSpacing.default,
  },
  subtextS: {
    fontSize: "10px",
    fontWeight: textStyles.fontWeight.regular,
    lineHeight: "14px",
    letterSpacing: textStyles.letterSpacing.default,
  },

  semiBoldLinkXL: {
    fontSize: "20px",
    fontWeight: textStyles.fontWeight.semibold,
    lineHeight: "28px",
    letterSpacing: textStyles.letterSpacing.default,
    textDecoration: "underline",
  },
  semiBoldLinkL: {
    fontSize: "16px",
    fontWeight: textStyles.fontWeight.semibold,
    lineHeight: "24px",
    letterSpacing: textStyles.letterSpacing.default,
    textDecoration: "underline",
  },
  semiBoldLinkM: {
    fontSize: "14px",
    fontWeight: textStyles.fontWeight.semibold,
    lineHeight: "20px",
    letterSpacing: textStyles.letterSpacing.default,
    textDecoration: "underline",
  },
  semiBoldLinkS: {
    fontSize: "12px",
    fontWeight: textStyles.fontWeight.semibold,
    lineHeight: "16px",
    letterSpacing: textStyles.letterSpacing.default,
    textDecoration: "underline",
  },
  semiBoldLinkXs: {
    fontSize: "10px",
    fontWeight: textStyles.fontWeight.semibold,
    lineHeight: "14px",
    letterSpacing: textStyles.letterSpacing.default,
    textDecoration: "underline",
  },

  regularLinkXL: {
    fontSize: "20px",
    fontWeight: textStyles.fontWeight.regular,
    lineHeight: "20px",
    letterSpacing: textStyles.letterSpacing.default,
    textDecoration: "underline",
  },
  regularLinkL: {
    fontSize: "16px",
    fontWeight: textStyles.fontWeight.regular,
    lineHeight: "24px",
    letterSpacing: textStyles.letterSpacing.default,
    textDecoration: "underline",
  },

  h1: {
    fontSize: "26px",
    fontWeight: 590,
    lineHeight: "32px",
  },
  h2: {
    fontSize: "22px",
    fontWeight: 590,
    lineHeight: "26px",
  },
  h3: {
    fontSize: "17px",
    fontWeight: 590,
    lineHeight: "22px",
  },
  h4: {
    fontSize: "15px",
    fontWeight: 590,
    lineHeight: "20px",
  },
  h5: {
    fontSize: "14px",
    fontWeight: 590,
    lineHeight: "20px",
  },
  headline: {
    fontSize: "13px",
    fontWeight: 590,
    lineHeight: "16px",
  },
  body: {
    fontSize: "13px",
    lineHeight: "16px",
    fontWeight: 400,
  },
  callout: {
    fontSize: "13px",
    fontWeight: 510,
    lineHeight: "15px",
  },
  subHeadline1: {
    fontSize: "14px",
    lineHeight: "20px",
    fontWeight: 400,
  },
  subHeadline2: {
    fontSize: "13px",
    lineHeight: "20px",
    fontWeight: 400,
  },
  footNote: {
    fontSize: "12px",
    lineHeight: "13px",
    fontWeight: 400,
  },
  caption1: {
    fontSize: "10px",
    lineHeight: "13px",
    fontWeight: 400,
  },
  caption2: {
    fontSize: "10px",
    lineHeight: "13px",
    fontWeight: 510,
  },
};

export const muiTheme = createTheme({
  palette: {
    primary: {
      main: "#1E221E",
      contrastText: "#ffffff",
    },
    secondary: {
      main: "#0A9083",
      contrastText: "#000000",
    },
    error: {
      main: "#ED1D31",
      contrastText: "#ffffff",
    },
    warning: {
      main: "#F3800D",
      contrastText: "#000000",
    },
    info: {
      main: "#0881EA",
      contrastText: "#000000",
    },
    success: {
      main: "#0AB22C",
      contrastText: "#000000",
    },
    background: {
      default: "#F7F9FC",
    },
  },
  typography: dialogTypography,
  components: {
    MuiTypography: {
      defaultProps: {
        variantMapping: {
          h1: "h1",
          h2: "h2",
          h3: "h3",
          h4: "h4",
          headline: "h5",
          body: "span",
          callout: "span",
          subHeadline1: "span",
          subHeadline2: "span",
          footNote: "span",
          caption1: "span",
          caption2: "span",
        },
      },
    },
    MuiButton: {
      defaultProps: {
        disableElevation: true,
        size: "large",
      },
      styleOverrides: {
        root: {
          textTransform: "none",
          fontSize: "14px",
          borderRadius: "8px",
        },
        text: {
          textDecoration: "underline",
          "&:hover": {
            backgroundColor: "transparent",
            textDecoration: "underline",
          },
          padding: "0px 8px",
          textAlign: "left",
        },
      },
    },
    MuiTab: {
      styleOverrides: {
        root: {
          textTransform: "none",
          fontSize: "14px",
        },
      },
    },
    MuiChip: {
      defaultProps: {
        size: "small",
      },
      styleOverrides: {
        root: {
          paddingLeft: "5px",
          paddingRight: "5px",
        },
      },
    },
    MuiPaper: {
      styleOverrides: {
        root: {
          borderRadius: "16px",
        },
      },
    },
    MuiCard: {
      defaultProps: {
        variant: "outlined",
      },
      styleOverrides: {
        root: {
          borderRadius: "16px",
        },
      },
    },
    MuiAutocomplete: {
      styleOverrides: {
        root: {
          "& .MuiAutocomplete-inputRoot": {
            paddingLeft: "14px",
          },
        },
      },
    },
    MuiLink: {
      styleOverrides: {
        root: {
          fontWeight: "bold",
          "&:hover": {
            cursor: "pointer",
          },
        },
      },
      defaultProps: {
        variant: "body",
      },
    },
    MuiTextField: {
      styleOverrides: {
        root: {
          "& .MuiInputBase-root": {
            borderRadius: "8px",
          },
        },
      },
    },
    MuiFormControl: {
      styleOverrides: {
        root: {
          "& .MuiInputBase-root": {
            borderRadius: "8px",
          },
        },
      },
    },
    MuiDrawer: {
      styleOverrides: {
        paper: {
          borderRadius: 0,
        },
      },
    },
  },
});
