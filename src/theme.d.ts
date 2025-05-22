import '@mui/material/Typography';

declare module '@mui/material/styles' {
  interface TypographyVariants {
    headline: React.CSSProperties;
    body: React.CSSProperties;
    callout: React.CSSProperties;
    subHeadline1: React.CSSProperties;
    subHeadline2: React.CSSProperties;
    footNote: React.CSSProperties;
    caption1: React.CSSProperties;
    caption2: React.CSSProperties;

    displayL: React.CSSProperties;
    displayM: React.CSSProperties;

    headingL: React.CSSProperties;
    headingM: React.CSSProperties;
    headingS: React.CSSProperties;

    semiBoldLabelL: React.CSSProperties;
    semiBoldLabelM: React.CSSProperties;
    semiBoldLabelS: React.CSSProperties;
    semiBoldLabelXs: React.CSSProperties;
    semiBoldLabelXxs: React.CSSProperties;

    regularLabelL: React.CSSProperties;
    regularLabelM: React.CSSProperties;
    regularLabelS: React.CSSProperties;
    regularLabelXs: React.CSSProperties;
    regularLabelXxs: React.CSSProperties;

    textXl: React.CSSProperties;
    textL: React.CSSProperties;
    textM: React.CSSProperties;
    subtextM: React.CSSProperties;
    subtextS: React.CSSProperties;

    semiBoldLinkXL: React.CSSProperties;
    semiBoldLinkL: React.CSSProperties;
    semiBoldLinkM: React.CSSProperties;
    semiBoldLinkS: React.CSSProperties;
    semiBoldLinkXs: React.CSSProperties;

    regularLinkXL: React.CSSProperties;
    regularLinkL: React.CSSProperties;
  }

  // allow configuration using `createTheme`
  interface TypographyVariantsOptions {
    headline?: React.CSSProperties;
    body?: React.CSSProperties;
    callout?: React.CSSProperties;
    subHeadline1: React.CSSProperties;
    subHeadline2: React.CSSProperties;
    footNote?: React.CSSProperties;
    caption1?: React.CSSProperties;
    caption2?: React.CSSProperties;

    displayL?: React.CSSProperties;
    displayM?: React.CSSProperties;

    headingL?: React.CSSProperties;
    headingM?: React.CSSProperties;
    headingS?: React.CSSProperties;

    semiBoldLabelL?: React.CSSProperties;
    semiBoldLabelM?: React.CSSProperties;
    semiBoldLabelS?: React.CSSProperties;
    semiBoldLabelXs?: React.CSSProperties;
    semiBoldLabelXxs?: React.CSSProperties;

    regularLabelL?: React.CSSProperties;
    regularLabelM?: React.CSSProperties;
    regularLabelS?: React.CSSProperties;
    regularLabelXs?: React.CSSProperties;
    regularLabelXxs?: React.CSSProperties;

    textXl?: React.CSSProperties;
    textL?: React.CSSProperties;
    textM?: React.CSSProperties;
    subtextM?: React.CSSProperties;
    subtextS?: React.CSSProperties;

    semiBoldLinkXL?: React.CSSProperties;
    semiBoldLinkL?: React.CSSProperties;
    semiBoldLinkM?: React.CSSProperties;
    semiBoldLinkS?: React.CSSProperties;
    semiBoldLinkXs?: React.CSSProperties;

    regularLinkXL?: React.CSSProperties;
    regularLinkL?: React.CSSProperties;
  }
}

// Update the Typography's variant prop options
declare module '@mui/material/Typography' {
  interface TypographyPropsVariantOverrides {
    headline: true;
    body: true;
    callout: true;
    subHeadline1: true;
    subHeadline2: true;
    footNote: true;
    caption1: true;
    caption2: true;

    displayL: true;
    displayM: true;

    headingL: true;
    headingM: true;
    headingS: true;

    semiBoldLabelL: true;
    semiBoldLabelM: true;
    semiBoldLabelS: true;
    semiBoldLabelXs: true;
    semiBoldLabelXxs: true;

    regularLabelL: true;
    regularLabelM: true;
    regularLabelS: true;
    regularLabelXs: true;
    regularLabelXxs: true;

    textXl: true;
    textL: true;
    textM: true;
    subtextM: true;
    subtextS: true;

    semiBoldLinkXL: true;
    semiBoldLinkL: true;
    semiBoldLinkM: true;
    semiBoldLinkS: true;
    semiBoldLinkXs: true;

    regularLinkXL: true;
    regularLinkL: true;
  }
}
